# Code-Based Ramp Secret Sharing — C reference implementation




| Scheme | Description | Code used |
|---|---|---|
| I   | K_n-based (t,n) ramp scheme | Reed–Solomon [m,k] MDS code over GF(1000003), m = n(n-1)/2 |
| II  | Generator-matrix-based (t,n) ramp scheme | Reed–Solomon [n,t] MDS code |
| III | Perfect-code-based (t+1,2t+1) ramp scheme | Binary Hamming [7,4], [31,26], [127,120] and Golay [23,12] |
| IV  | Tompa–Woll-resistant variant of Scheme I | as Scheme I |

## Build and run

Requires only a C compiler (gcc/clang) and the math library.

```bash
make            # or: gcc -O2 -Wall -o ramp_sss ramp_sss.c -lm
./ramp_sss          # correctness tests + Tompa–Woll tampering experiment
```


## What the tests check

* Schemes I/II: any `t` participants recover the secret; `t-1` hold fewer than `k` coordinates (Scheme I) and cannot.
* Scheme III: for every subset of the `2t+1` participants, authorized subsets (size >= t+1) recover the secret and unauthorized subsets decode to a different codeword. The code verifies at run time that each code is perfect (the syndrome table has exactly 2^(m-k) distinct coset leaders of weight <= t). It also enumerates the secret space (Golay: 4094 of 4096 codewords).
* Tompa–Woll experiment (n=8, t=4): a tampered edge to a non-member is accepted silently in Scheme I, has no effect in Scheme IV; a tampered edge between coalition members is detected in both.

Expected last line of `./ramp_sss`: `ALL TESTS PASSED`. Secrets and helper vectors are random, so intermediate values differ between runs.

## Notes

* This is a research prototype. It uses `rand()` and a small fixed prime field and is not hardened (no constant-time arithmetic, no secure randomness). Do not use it to protect real secrets.
* Scheme IV has information rate k/(n-1) with k <= C(t,2); this exceeds 1 only when C(t,2) > n-1.




```
