# Lower bounds for hypothesis testing based on information theory

The goal of this project is to formalize in Lean the definitions and properties of information divergences between probability measures, as well as results about error bounds for (sequential) hypothesis testing.

For a detailed presentation, see the blueprint at https://remydegenne.github.io/testing-lower-bounds/blueprint/index.html

### Contents
- Definitions of divergences between measures: f-divergence, Kullback-Leibler (or relative entropy), Rényi, TV, DeGroot statistical information
- Definition of an estimation task and its risk
- Proofs of the data-processing inequality for f-divergences (in progress)

### Technical note

To do a Mathlib bump without breaking the blueprint, use `lake -R -Kenv=dev update`
