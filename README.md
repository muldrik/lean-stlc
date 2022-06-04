# Typechecker for STLC in Lean4

## Quick start
  - Install Lean4 and the language server following [the online instruction](https://leanprover.github.io/lean4/doc/quickstart.html). Last testes version is `lean4:nightly-2022-05-29`
  - Open `Typecheker.lean`
  - Interact

## Supported syntax for evaluation

### Term
A term can be constructed inside ⟪ ⟫ notation (use \\<< and \\>> for brackets with LSP)

Examples:

```lean
⟪ x ⟫
⟪ x y ⟫
⟪ λ x : a, x ⟫
⟪ (λ x : a, x) y ⟫
⟪ (λ x : (α → β) → γ, x) (λ y : α → β, z) ⟫
```

### Type
Types can be constructed inside a term or a context, using a standard notation: strings, arrows (\to) and brackets


### Context
A context can be constructed with ⦃⦄ notation, use \\{{ and \\}} for brackets

Examples:
```lean
⦃⦄ -- empty context
⦃z : γ⦄ -- context where variable z has type γ
⦃ x : α → β, y : α ⦄ -- declarations are separated with a comma
```

All expressions can be evaluated with `#eval` and will be pretty-printed

```lean
#eval ⟪ λ x : a, x ⟫
-- Lean infoview:
-- λ x : a, x
```

### Typechecking

`Term.typecheck` accepts a context and a term and returns a type if it has been found. `Option` is used for the return type. The type is pretty-printed if used with `#eval`

```lean
#eval Term.typecheck ⦃⦄ ⟪ λ x : a, λ y : b, λ z : d, x ⟫
-- a → b → d → a

#eval Term.typecheck ⦃x : a → b → c⦄ ⟪ x ⟫
-- a → b → c

#eval Term.typecheck ⦃z : γ⦄ ⟪ (λ x : (α → β) → γ, x) (λ y : α → β, z) ⟫
-- (α → β) → γ
```


## Correctness

Completeness and soundness of `Term.typecheck` are proven in `typecheck_complete` and `typecheck_sound` theorems respectively. This also guarantees that type inference is decidable