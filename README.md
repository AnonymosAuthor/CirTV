This project is primarily designed to verify the correctness of compilation results from the Circom compiler, consisting of the following main components:

## 1. Compiler-Verification-ForASE2025

**(1) Verifier**

Implements the core verification functionality.

**(2) Astbuilder**

The `Astbuilder` source code, which is modified from the Circom compiler source code. Used to extract JSON-formatted abstract syntax trees from Circom source code.

### 1.1 Environment Dependencies

To develop this project, please ensure the appropriate environment is set up. The recommended environment matches our current setup, though reasonable alternatives should also work.

**(1) Operating System**

Linux, recommended Ubuntu 22.04

**(2) Rust Development Environment**

If you don't plan to modify the existing Astbuilder executable provided in `RAW/Verifier/dependence/`, you won't need a Rust environment.

If required, recommended version: Rust 1.78.0

**(3) Python3 Environment**

Recommended version: 3.10.12

**(4) CVC5 Solver**

We recommend downloading the latest CVC5 solver source code from GitHub and compiling it following the official instructions (remember to include the finite field logic).

### 1.2 Usage

**(1) Verifier**

The main function is located in `RAW/Verifier/main.py`. You can run commands in the console to verify the correctness of specific Circom files.

Users can specify the file path, Circom compiler optimization level (O0, O1, O2), and elliptic curve name. The file path is mandatory, while the other two parameters are optional and will use default values if omitted. For example:

```
python3.10 main.py circom_file_path --polish O0 --prime bn128
```
**(2) Astbuilder**

Open `RAW/Verifier/dependence`, the `AstBuilder` without any suffix is the entrance we prepared to extract the abstract syntax tree of the Circom program.
