# Isabelle-Arithmetization
Formalization of Sigma11 and related in Isabelle/HOL

## Usage with Nix

To get a dev shell:

```
nix develop
```

To build the theories in the dev shell:

```
isabelle build -D theories
```

To build the theories outside the dev shell:

```
nix build
```
