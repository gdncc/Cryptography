SHA-3 / SHAKE test vectors (`sha-3bytetestvectors/`, `shakebytetestvectors/`) are from
[NIST CAVP](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing).

Keccak test vectors (`keccakbytetestvectors/`) are derived from the original
KeccakKAT files published by the Keccak Team (Bertoni, Daemen, Peeters,
Van Assche), specifically the `ShortMsgKAT_*.txt` and `LongMsgKAT_*.txt`
files for original-padding Keccak-224/256/384/512. They were obtained
via the [damaki/libkeccak](https://github.com/damaki/libkeccak) mirror
under `tests/kat/testvectors/Keccak/`, filtered to byte-aligned message
lengths and reformatted as NIST CAVS-style `.rsp` files (uppercase MDs
lowercased, `[L = …]` header added) so the existing `slurpMsgFile`
parser can read them.
