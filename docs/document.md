# Cubical Lambda — Project Documentation

## Overview

This project is a minimal implementation of **Cubical Type Theory** in Haskell, inspired by the Cartesian Cubical Computational Type Theory (CCHM) style. It provides:

- A core language with dependent types, path types, Kan composition, and Glue types
- A bidirectional type checker
- A hand-written parser with Unicode support
- A command-line driver that checks terms read from files

The implementation is split across three modules: `CubicalLambda`, `Parser`, and `main`.

---

## Module Overview

| File | Module | Purpose |
|---|---|---|
| `CubicalLambda.hs` | `CubicalLambda` | Core AST, evaluator, substitution, type checker |
| `Parser.hs` | `Parser` | Lexer and parser for surface syntax |
| `main.hs` | *(executable)* | CLI driver: reads files and type-checks each term |

---

## Module: `CubicalLambda`

### Interval Syntax and DNF

The **interval** (`𝕀`) is the unit interval of cubical type theory. Interval expressions support the structure of a De Morgan algebra:

```
data I
  = I0 | I1           -- endpoints 0 and 1
  | IVar Int          -- variable iₙ
  | Meet I I          -- i ∧ j
  | Join I I          -- i ∨ j
  | Neg I             -- ¬i
```

Interval expressions are normalized into **Disjunctive Normal Form (DNF)**:

```haskell
newtype DNF = DNF { getCubes :: Set (Set Literal) }
```

Each `Set Literal` is a *cube* (a conjunction of literals), and the outer `Set` is a disjunction. The DNF representation enables efficient simplification and comparison.

Key DNF operations:

| Function | Description |
|---|---|
| `evalInterval` | Converts an `I` expression to its DNF normal form |
| `dnfJoin` | Union of two DNFs (disjunction), with subsumption simplification |
| `dnfMeet` | Pairwise union of cubes (conjunction), with simplification |
| `dnfNeg` | De Morgan negation: distributes negation over all literals |
| `simplify` | Removes any cube subsumed by a smaller cube in the set |

---

### Term AST

The core language is represented by the `Term` type using **de Bruijn indices** — variables are integers counting the number of binders between the use site and the binding site. Name hints (`type Name = String`) are carried alongside binders purely for pretty-printing.

```haskell
data Term
  = TVar Int              -- de Bruijn variable
  | TApp Term Term        -- function application
  | TAbs Name Term        -- λ-abstraction
  | TUniv Level           -- universe Uₙ
  | TIntervalTy           -- the pseudo-type 𝕀
  | TPi Name Term Term    -- dependent product Π(x:A).B
  | TInterval I           -- symbolic interval expression
  | TCube DNF             -- normalized interval (normal form of TInterval)
  | TPath Term Term Term  -- Path type: Path A u v
  | PLam Name Term        -- path abstraction ⟨i⟩ t
  | PApp Term Term        -- path application: t @ r
  | THComp Term Term Term Term   -- hcomp A φ u u₀
  | TGlue Term Term Term         -- Glue A φ T_e
  | TGlueElem Term Term Term     -- glue φ t a
  | TUnglue Term Term Term       -- unglue φ T_e g
```

#### Glue Types

Glue types are the mechanism that makes **univalence** possible. They allow a type to be "glued" from a base type and a partial type on a face of the cube.

**`TGlue A φ T_e`** — Glue type formation:

```
Γ ⊢ A : Uₙ    Γ ⊢ φ : 𝕀    Γ, φ ⊢ T_e : Σ(T:Uₙ). Equiv T A
────────────────────────────────────────────────────────────────
Γ ⊢ Glue A φ T_e : Uₙ
```

β-rules:
- `Glue A ⊤ (T, e)  ≡  T`
- `Glue A ⊥ _       ≡  A`

**`TGlueElem φ t a`** — glue element introduction:

```
Γ ⊢ φ : 𝕀    Γ, φ ⊢ t : T    Γ ⊢ a : A    φ ⊢ e(t) ≡ a
────────────────────────────────────────────────────────────
Γ ⊢ glue φ t a : Glue A φ (T, e)
```

β-rules:
- `glue ⊤ t a  ≡  t`
- `glue ⊥ t a  ≡  a`

**`TUnglue φ T_e g`** — unglue element elimination:

```
Γ ⊢ g : Glue A φ T_e
─────────────────────
Γ ⊢ unglue φ T_e g : A
```

β-rules:
- `unglue ⊤ (T,e) g  ≡  e(g)`
- `unglue ⊥ _ g      ≡  g`

---

### Substitution and Evaluation

#### `shift :: Int -> Int -> Term -> Term`

Increments all free de Bruijn indices ≥ `c` by `d`. Used to "lift" a term under a new binder without accidentally capturing free variables.

- `d` — the increment amount (usually +1)
- `c` — the cutoff index below which variables are treated as bound

#### `subst :: Int -> Term -> Term -> Term`

Replaces every free occurrence of de Bruijn index `j` in a term with the substitution term `s`. When descending under a binder, `s` is shifted to account for the new binding level.

#### `beta :: Term -> Term -> Term`

Performs a single β-reduction step: substitutes de Bruijn 0 in `body` with `arg`, then lowers all remaining free indices by 1 (since the binder has been consumed).

```haskell
beta body arg = shift (-1) 0 (subst 0 (shift 1 0 arg) body)
```

#### `eval :: Term -> Term`

Normalizes a term to **normal form** by repeatedly applying β-reductions and cubical β-rules. Key reductions handled:

| Constructor | Reduction |
|---|---|
| `TApp (TAbs _ body) a` | Ordinary β-reduction |
| `PApp (PLam _ body) r` | Path β-reduction: substitute interval endpoint |
| `THComp _ ⊤ (PLam _ body) _` | `hcomp` at ⊤: evaluate tube at `i=1` |
| `THComp _ ⊥ _ base` | `hcomp` at ⊥: return base |
| `TGlue _ ⊤ te` | Glue at ⊤: reduce to fibre type |
| `TGlue _ ⊥ _` | Glue at ⊥: reduce to base type |
| `TGlueElem ⊤ t _` | `glue` at ⊤: return partial element |
| `TGlueElem ⊥ _ a` | `glue` at ⊥: return base element |
| `TUnglue ⊤/⊥ _ g` | Both reduce to `g` (identity equivalence) |

---

### Bidirectional Type Checker

The type checker uses a standard **bidirectional** discipline:

- **Inference** (`infer :: Ctx -> Term -> Either TypeError Term`): synthesizes the type of a term.
- **Checking** (`check :: Ctx -> Term -> Term -> Either TypeError ()`): verifies a term against a given type.

The typing context is:

```haskell
type Ctx = [(Name, Term)]
```

A stack of name–type pairs. The head is de Bruijn index 0. When a type is retrieved at depth `i`, it is shifted by `i+1` to be valid at the current context depth.

#### Inference Rules Summary

| Term | Rule |
|---|---|
| `TVar i` | Lookup in context, shift by depth |
| `TUniv n` | `Uₙ ⇒ Uₙ₊₁` |
| `TApp f a` | Infer `f : Π(x:A).B`, check `a : A`, return `B[0:=a]` |
| `TPi x A B` | Infer universes of `A` and `B`, return `U_{max i j}` |
| `TPath A u v` | Infer universe of `A`, check endpoints, return same universe |
| `PApp p r` | Infer `p : Path A u v`, check `r : 𝕀`, return `A` |
| `TGlue A φ T_e` | Infer universes, check φ is interval, return `U_{max n m}` |
| `TUnglue φ T_e g` | Infer `g : Glue A φ T_e`, return `A` |
| `THComp A φ u u₀` | Require `A : Uₙ`, check tube and base, return `A` |
| `TAbs`, `PLam` | Cannot infer — require `check` with annotation |

#### Checking Rules Summary

| Term | Rule |
|---|---|
| `TAbs x body` | Expect `Π(x:A).B`; check `body : B` under extended context |
| `PLam i body` | Expect `Path A u v`; check endpoints match, check body under interval variable |
| `TGlueElem φ t a` | Expect `Glue A φ T_e`; check `t : T_e` and `a : A` |
| *(anything else)* | Subsumption: infer type and compare definitionally |

#### Type Errors

```haskell
data TypeError
  = UnboundVariable Name
  | TypeMismatch Term Term   -- expected vs. got
  | ExpectedPi Term
  | ExpectedPath Term
  | ExpectedUniverse Term
  | NotAnInterval Term
  | CannotInfer Term
  | Other String
```

---

### Top-level Helpers

| Function | Signature | Description |
|---|---|---|
| `inferClosed` | `Term -> Either TypeError Term` | Infer type in empty context |
| `checkClosed` | `Term -> Term -> Either TypeError ()` | Check type in empty context |
| `reportInfer` | `String -> Term -> IO ()` | Print inference result with label |
| `reportCheck` | `String -> Term -> Term -> IO ()` | Print check result with label |
| `definitionallyEqual` | `Term -> Term -> Bool` | Normalize both terms and compare |

---

## Module: `Parser`

### Parser Monad

The parser is built on a hand-rolled `Parser` monad:

```haskell
newtype Parser a = Parser { runParser :: String -> Either ParseError (a, String) }
```

It implements `Functor`, `Applicative`, and `Monad`. Backtracking is explicit via `try`:

```haskell
try :: Parser a -> Parser (Maybe a)
```

The `(<|>)` operator tries the left parser first; on failure (without consuming input), it falls back to the right.

### Interval Parser

Entry point: `parseInterval :: String -> Either ParseError I`

Parses a full interval expression using a standard precedence hierarchy:

```
iExpr  ::=  iJoin
iJoin  ::=  iMeet (∨ iMeet)*
iMeet  ::=  iNeg  (∧ iNeg)*
iNeg   ::=  ¬ iNeg | iAtom
iAtom  ::=  0 | 1 | i<n> | '(' iExpr ')'
```

### Term Parser

Entry point: `parseTerm :: String -> Either ParseError Term`

The surface grammar resolves de Bruijn indices at parse time using a name environment (`Env = [Name]`). The grammar is:

```
term  ::=  λx. term        (lambda abstraction)
        |  ⟨x⟩ term        (path abstraction)
        |  Π(x:A). B       (dependent product)
        |  app

app   ::=  atom (@ atom | atom)*   (left-associative application / path application)

atom  ::=  U<n>                    (universe)
        |  𝕀                       (interval pseudo-type)
        |  i<n> | 0 | 1            (interval literals)
        |  hcomp A [φ] u u₀
        |  Glue A [φ] te
        |  glue [φ] t a
        |  unglue [φ] te g
        |  Path A u v
        |  <name>                  (variable, resolved to de Bruijn index)
        |  '(' term ')'
```

Multi-argument forms (`hcomp`, `Glue`, `glue`, `unglue`, `Path`) must be parenthesized when used as arguments inside a larger expression.

#### Unicode Symbols Used

| Symbol | Unicode | Meaning |
|---|---|---|
| `λ` | U+03BB | Lambda abstraction |
| `Π` | U+03A0 | Dependent product |
| `⟨⟩` | U+27E8/27E9 | Path abstraction brackets |
| `∧` | U+2227 | Meet (interval conjunction) |
| `∨` | U+2228 | Join (interval disjunction) |
| `¬` | U+00AC | Negation |
| `𝕀` | U+1D540 | Interval pseudo-type |

---

## Module: `main`

The executable entry point. Accepts one or more file paths as command-line arguments.

### File Format

Each file is processed line by line:
- **Blank lines** are skipped.
- **Lines beginning with `--`** are treated as comments and skipped.
- **All other lines** are parsed and type-checked as terms.

### Example Usage

```
$ cubical terms.ctt
```

Each line is parsed with `parseTerm`, then type-checked with `inferClosed`. Results are printed with line numbers.

### Output Format

A successful line produces:
```
[line N]   parse  "..."
    => <pretty-printed term>
    : <inferred type>
```

A parse or type error produces:
```
[line N]   parse  "..."
    PARSE ERROR: ...
    TYPE ERROR: ...
```

---

## Architecture Diagram

```
┌─────────────┐     parseTerm      ┌───────────────────┐
│ Source Text │ ─────────────────► │   Parser.hs       │
└─────────────┘                    │  (Parser monad,   │
                                   │  name → de Bruijn)│
                                   └────────┬──────────┘
                                            │ Term (AST)
                                            ▼
                                   ┌───────────────────┐
                                   │  CubicalLambda.hs │
                                   │                   │
                                   │  eval (normalize) │
                                   │  infer / check    │
                                   │  shift / subst    │
                                   │  beta-reduction   │
                                   └────────┬──────────┘
                                            │ Either TypeError Term
                                            ▼
                                   ┌───────────────────┐
                                   │    main.hs        │
                                   │  (CLI, file I/O,  │
                                   │   reportInfer)    │
                                   └───────────────────┘
```

---

## Key Design Decisions

**De Bruijn indices.** All semantic operations (substitution, shifting, type checking) work with nameless indices. Name strings are carried as hints solely for pretty-printing and have no semantic effect.

**Bidirectional type checking.** Introduction forms (`TAbs`, `PLam`, `TGlueElem`) are *checked* against a known type; elimination forms and type constructors *synthesize* a type. Subsumption falls back to inference + definitional equality.

**Definitional equality via normalization.** Two terms are definitionally equal if and only if `eval t1 == eval t2`. The evaluator is call-by-value and reduces all β-redexes including cubical ones (hcomp, Glue, glue, unglue).

**Simplified Glue.** In full CCHM, `T_e` must be `Σ(T:U). Equiv T A`. This implementation accepts any `T_e : Uₙ` and treats `unglue` at ⊤ as the identity equivalence, making univalence structurally present but not fully enforced.

**DNF normalization for intervals.** Interval expressions are always reduced to DNF. This makes face comparisons (⊤/⊥ detection) and subsumption-based simplification straightforward and efficient.