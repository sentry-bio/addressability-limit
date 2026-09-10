# Manuscript artifacts

- `addressability-limit.pdf` is the current mathematical manuscript.
- `addressability-limit-overview.pdf` is the expository companion.

The repository does not yet contain the LaTeX, bibliography, figure, or build
inputs that generated these PDFs. Consequently the manuscript is readable but
not reproducible from this checkout. Before an archival release, add those
inputs here together with a deterministic build command and record the resulting
PDF hashes.

Until then, theorem numbering in repository documentation follows the PDFs
dated August 28, 2026:

- relational capacity of real hyperbolic space: Theorem 5.3;
- isotropic Heintze classification under A3: Proposition 6.2;
- curvature floor: Theorem 6.4;
- saturation statement: Proposition 7.1.

The Lean kernel now states the Structured Addressability Limit
`β ≤ C_𝒜 ≤ C_block = c h_pack` under depthwise recoding, with uniform local
finiteness as the relational source class. The PDFs still present the older
ladder-plus-profile architecture and do not yet name ULF, Tessera–Cornulier,
or Kerr. See `../STATUS.md` for the claim-by-claim status and release gates.
