import os
import sys
import subprocess
from pathlib import Path
from glob import glob
from concurrent.futures import ProcessPoolExecutor, as_completed
from threading import Lock
from collections import Counter
import uuid
from tqdm import tqdm

# Shared counters and locks
counter = Counter()
counter_lock = Lock()
error_log_lock = Lock()
invalid_log_lock = Lock()


def remove_first_unsat_line(file_path):
    """Remove the first line if it says 'unsat'."""
    with open(file_path, 'r') as f:
        lines = f.readlines()
    if lines and lines[0].strip() == 'unsat':
        with open(file_path, 'w') as f:
            f.writelines(lines[1:])


def process_file(a_path_str):
    """Process a single .alethe file and its corresponding .smt2 file."""
    a_path = Path(a_path_str)
    s_path = a_path.with_suffix('.smt2')

    local_counter = Counter()
    errors = []
    invalids = []

    if not s_path.exists():
        return local_counter, errors, invalids

    remove_first_unsat_line(a_path)

    with open(a_path, 'r') as f:
        for line in f:
            if line.startswith('(step '):
                parts = line.strip().split()
                if len(parts) < 2:
                    continue
                step_id = parts[1]

                for max_distance in range(1, 11):  # 1 to 10 inclusive
                    suffix = f"{os.getpid()}_{uuid.uuid4().hex[:8]}"
                    temp_a = f"temp_{suffix}.alethe"
                    temp_s = f"temp_{suffix}.smt2"

                    # Run carcara slice (suppress stdout) with --max-distance
                    slice_cmd = [
                        'carcara', 'slice', str(a_path), str(s_path),
                        temp_a, temp_s, '--from', step_id,
                        '--max-distance', str(max_distance)
                    ]
                    slice_result = subprocess.run(
                        slice_cmd,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.PIPE,
                        text=True
                    )

                    # Run carcara check
                    check_cmd = ['carcara', 'check', temp_a, temp_s, '--ignore-unknown-rules']
                    check_result = subprocess.run(check_cmd, capture_output=True, text=True)
                    output = check_result.stdout.strip()
                    returncode = check_result.returncode

                    if returncode != 0:
                        error_entry = (
                            f"ERROR: {a_path} {s_path} step={step_id} max-distance={max_distance}\n"
                            f"{slice_result.stderr}\n"
                            f"{check_result.stderr}\n"
                        )
                        errors.append(error_entry)
                    else:
                        if output == "valid":
                            local_counter["valid"] += 1
                        elif output == "invalid":
                            local_counter["invalid"] += 1
                            invalids.append(
                                f"INVALID: {a_path} {s_path} step={step_id} max-distance={max_distance}\n"
                            )
                        elif output == "holey":
                            local_counter["holey"] += 1

                    for temp_file in [temp_a, temp_s]:
                        try:
                            os.remove(temp_file)
                        except FileNotFoundError:
                            pass

    return local_counter, errors, invalids


def main(input_dir):
    if not input_dir or not os.path.isdir(input_dir):
        print("Usage: python3 slice.py /path/to/input_dir")
        sys.exit(1)

    alethe_files = glob(os.path.join(input_dir, '**', '*.alethe'), recursive=True)

    with ProcessPoolExecutor() as executor:
        futures = [executor.submit(process_file, str(a)) for a in alethe_files]

        with tqdm(total=len(futures), desc="Processing files") as pbar:
            for future in as_completed(futures):
                local_counter, errors, invalids = future.result()

                with counter_lock:
                    counter.update(local_counter)

                if errors:
                    with error_log_lock:
                        with open('error.log', 'a') as ef:
                            ef.writelines(errors)

                if invalids:
                    with invalid_log_lock:
                        with open('invalid.log', 'a') as inf:
                            inf.writelines(invalids)

                pbar.update(1)

    with open('result.log', 'w') as f:
        f.write(f"valid: {counter['valid']}\n")
        f.write(f"invalid: {counter['invalid']}\n")
        f.write(f"holey: {counter['holey']}\n")


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else '')
