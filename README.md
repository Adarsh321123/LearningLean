# Learning Lean

## Overview

This repo contains some of the code I wrote to learn Lean (theorem prover) for my research in the Caltech Anima Lab on [LeanAgent](https://arxiv.org/abs/2410.06209). This involved following the [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) and [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) textbooks, the [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) repository, and a bit of the [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html) textbook.

## Usage

Please see Lean's [installation instructions](https://leanprover-community.github.io/get_started.html), switch to version `v4.6.0-rc1`, and run the following

```
git clone https://github.com/Adarsh321123/LearningLean.git
cd LearningLean
lake exe cache get
lake build
```

Note that these commands may take a bit to run as building Lean can be pretty slow.
