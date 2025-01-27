# Use the Rust official image
FROM rust:1.72
WORKDIR /carcara

# Copy the files in your machine to the Docker image
COPY ./ ./

# Build your program
RUN cargo build --release --verbose

# Entrypoint for the container
CMD ["/bin/bash"]