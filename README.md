# Lower bounds for hypothesis testing based on information theory

> [!WARNING]
> **This repository is no longer maintained. Its code has been migrated to [Statlib](https://github.com/stat-lib/statlib).**
>
> If your project depends on this repository, please depend on Statlib instead. In your `lakefile.toml`:
>
> ```toml
> [[require]]
> name = "Statlib"
> git = "https://github.com/stat-lib/statlib"
> rev = "main"
> ```

The goal of this project is to formalize in Lean the definitions and properties of information divergences between probability measures, as well as results about error bounds for (sequential) hypothesis testing.

For a detailed presentation, see the blueprint at https://remydegenne.github.io/testing-lower-bounds/blueprint/index.html

### Contents
- Definitions of divergences between measures: f-divergence, Kullback-Leibler (or relative entropy), Rényi, TV, DeGroot statistical information
- Definition of an estimation task and its risk
- Proofs of the data-processing inequality for f-divergences
