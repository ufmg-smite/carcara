# Proof template directory

This directory contains the files necessary for segmented Lambdapi proof, see `cargo translate --help` for more information.

## Usage

To check the proof, change into the generated proof directory and in that directory run the command:

```sh
make -j [N]
```

## Structure of the template

* `lambdapi.pkg` Lambdapi package file. A package determine the name space under which the objects of the package will be made accessible to other objects of the package. The name space is defined as the name of the proof.
* `lpo.mk` generated makefile that contains all the dependencies between segment.
* `Makefile` use to check a segmented proof with N jobs at once (multiprocess check).