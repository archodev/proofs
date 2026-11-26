# Source provenance

The mathematical question comes from [Axenovich, Liu and Sagdeev,
Question 3](https://arxiv.org/html/2512.15516v3#S6.SS1).

The files under `OAI/` and the four files under `Erdos173/` are from
[Plasma AI's Lean formalization of Erdős problem 173, pinned revision
`bc41fe8950bafe3d69fc58f2a422f1dee9a1e943`](https://github.com/plasma-ai/erdos-173/tree/bc41fe8950bafe3d69fc58f2a422f1dee9a1e943).
The supplied Lean files at those paths are byte-for-byte copies. The
stationary law, shift action and unitary representation in `C5/Model.lean`
adapt code from its `Erdos173/Transfer/LabelModel.lean` to the space of
five-cycle-avoiding labels. The copied Erdos173 files are `Basic.lean`,
`Measurable/Density.lean`, `Measurable/SelfSupport.lean` and
`Measurable/Boundary.lean`.

Plasma's port and generalization of the OpenAI modules records its changes
and individual credits in [OAI/README.md](OAI/README.md). That document
describes Plasma's full tree. This bundle includes the import closure used
here. The original source is [OpenAI's formalization at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
In particular the Haar-rigidity result is `finite_wild_fourier` in
`OAI/Analysis/PlaneSpectrum/Ergodicity.lean`. These sources and their
adaptations are distributed under [Apache License 2.0](LICENSE-upstream).

Stock Lean and Mathlib are resolved from the toolchain and package lockfile.

## Antecedent constructions and notices

The measurable density-boundary and irrational-rotation method, and the
binary-color transfer method, also appear in the [Plasma AI proof of
Erdős problem 173](https://github.com/plasma-ai/erdos-173/blob/bc41fe8950bafe3d69fc58f2a422f1dee9a1e943/blueprint/proof.md).
That result concerns triangles. The two-circle constraints for a five-cycle
and the concluding five-cycle contradiction are in the C5 sources here.
The Haar-rigidity input and the continuous-vector projection come from
[OpenAI, The Euclidean plane is not five-colorable, Theorem 2.3 and §4](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf).

The historical `OAI/README.md` counts 36 modules in the Plasma project.
This import closure contains 34 of those modules. Of these, 32 are Plasma
ports of files from OpenAI and two are Plasma's `Carrier` and `Carriers`
modules. The latter also adapts OpenAI code. The two files in the
upstream tree outside this import closure are `CircleDecay.lean` and
`Fourier.lean`.

The root Plasma license is preserved as `LICENSE-upstream`. The file
`OAI/LICENSE` is identical to both Plasma's `OAI/LICENSE` and OpenAI's
`lean/LICENSE`. Both license files contain Apache License 2.0. The
corresponding upstream trees contain no separate NOTICE file applying
to these paths. Original module notices and the attribution for the
adaptation of Plasma code in `C5/Model.lean` are retained. The prior C5 project supplied
no project-wide license for its newly written code.
