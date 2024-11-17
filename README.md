# Cryptography
Lean 4 programming language and theorem prover cryptography experiments

> [!CAUTION]
> :warning: **Under no circumstances should this be used for cryptographic
applications.** :warning:
> 
> This is an educational resource. The intended use of this project
> is for learning and experimenting with cryptography using Lean 4.

## SHA-3 Hash Functions

For now, the repository contains the implementation of four cryptographic hash
functions, SHA3-224, SHA3-256, SHA3-384, and SHA3-512, and two extendable-output
functions (XOFs), SHAKE128 and SHAKE256 of the SHA-3 family of functions in pure
Lean 4. It provides one-shot, and streaming APIs.

The library makes use of many Lean 4 features, including dependent typing, type
classes, and proofs.

File [example.lean](Cryptography/Hashes/SHA3/example.lean) shows sample usage of
the API. Build and run:

`lake build Cryptography.Hashes.SHA3.example && ./.lake/build/bin/Cryptography-Hashes-SHA3-example`

The implementation passes the test vectors from
[NIST](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing). The
test output must be reviewed manually:

`lake build Cryptography.Hashes.SHA3.test && ./.lake/build/bin/Cryptography-Hashes-SHA3-test`

Some performance testing code is included. Loops cannot be unrolled for now, if
one cares about proving some code properties, because of an
[issue](https://github.com/leanprover/lean4/issues/5324) with Lean's elaborator.

`lake build Cryptography.Hashes.SHA3.perftest && ./.lake/build/bin/Cryptography-Hashes-SHA3-perftest`

All array accesses are formally proven to be within bounds. 
