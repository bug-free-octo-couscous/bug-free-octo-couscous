# Cubical Lambda — Grammar Guide

This guide explains the full surface syntax of Cubical Lambda, with examples
drawn from the test suite. After reading this you should be able to write any
well-formed term without hitting a parse error.

---

## Table of Contents

1. [Quick-start cheatsheet](#1-quick-start-cheatsheet)
2. [File format](#2-file-format)
3. [Lexical basics — names, keywords, whitespace](#3-lexical-basics)
4. [Unicode symbols you need](#4-unicode-symbols)
5. [Interval expressions](#5-interval-expressions)
6. [Term grammar — the big picture](#6-term-grammar)
7. [Binders — λ, Π, ⟨⟩](#7-binders)
8. [Application and path application](#8-application-and-path-application)
9. [Atoms — the building blocks](#9-atoms)
10. [The parenthesisation rule](#10-the-parenthesisation-rule)
11. [Cubical constructs in detail](#11-cubical-constructs-in-detail)
12. [Common mistakes and how to fix them](#12-common-mistakes)

---

## 1. Quick-start cheatsheet

| What you want to write | Syntax |
|---|---|
| Universe level *n* | `U0` `U1` `U2` … |
| Interval pseudo-type | `𝕀` |
| Interval endpoint | `0` or `1` |
| Interval variable | `i0` `i1` `i2` … |
| Lambda | `λx. body` |
| Dependent product | `Π(x:A). B` |
| Path type | `Path A u v` |
| Path abstraction | `⟨i⟩ body` |
| Path application | `t @ r` |
| Kan composition | `hcomp A [φ] u u0` |
| Glue type | `Glue A [φ] T` |
| Glue element | `glue [φ] t a` |
| Unglue element | `unglue [φ] T g` |
| Parenthesise anything | `( … )` |

---

## 2. File format

The CLI reads your source file line by line:

```
-- This is a comment and is ignored entirely.

-- Blank lines are also ignored.

U0                          -- this line is parsed and type-checked
Π(A:U0). Π(x:A). A         -- so is this one
```

Rules:
- Lines that start with `--` are **comments** — skipped entirely.
- **Blank lines** are skipped.
- Every other line is **one complete term**, parsed and type-checked independently.

There is no multi-line syntax. If a term is too long it still has to live on one line.

---

## 3. Lexical basics

### Identifiers (names)

A name starts with a **letter or underscore**, then continues with letters,
digits, underscores, or single-quotes.

```
x       -- valid
myVar   -- valid
x'      -- valid (prime is allowed after the first char)
_foo    -- valid
i0      -- NOT a name — it is an interval literal (see below)
U2      -- NOT a name — it is a universe
```

### Keywords

The following words are **reserved** and cannot be used as variable names:

```
Path   hcomp   Glue   glue   unglue
```

A keyword is only recognised when it is **not immediately followed** by a letter,
digit, or underscore. So `Glue` is the keyword, but `GlueExtra` would be parsed
as a plain name (if it were in scope).

### Whitespace

Whitespace (spaces, tabs, newlines within a token stream) is ignored everywhere
between tokens. You can add as much spacing as you like for readability.

---

## 4. Unicode symbols

You will need to type these characters. Most editors let you insert them via
copy-paste or a Unicode input method.

| Symbol | Codepoint | What it does |
|:---:|---|---|
| `λ` | U+03BB | Starts a lambda abstraction |
| `Π` | U+03A0 | Starts a dependent product |
| `⟨` | U+27E8 | Opens a path abstraction binder |
| `⟩` | U+27E9 | Closes a path abstraction binder |
| `𝕀` | U+1D540 | The interval pseudo-type |
| `@` | U+0040 | Path application operator |
| `∧` | U+2227 | Interval meet (and) |
| `∨` | U+2228 | Interval join (or) |
| `¬` | U+00AC | Interval negation (not) |

---

## 5. Interval expressions

The interval `𝕀` is the unit interval of cubical type theory. Interval
*expressions* appear inside `[…]` brackets in `hcomp`, `Glue`, `glue`, and
`unglue`. They have their own mini-grammar, separate from the term grammar.

### Atoms

```
0           -- the bottom endpoint (falsy face)
1           -- the top endpoint (truthy face)
i0  i1  i2  -- named interval variables (i followed by one or more digits)
( expr )    -- parenthesised sub-expression
```

### Operators — precedence low → high

| Operator | Symbol | Meaning | Associativity |
|---|:---:|---|---|
| Join | `∨` | logical or / union of faces | left |
| Meet | `∧` | logical and / intersection of faces | left |
| Negation | `¬` | flip the face | right (prefix) |

So `¬i0 ∧ i1 ∨ i2` parses as `((¬i0) ∧ i1) ∨ i2`.

### Examples

```
[i0]            -- the bottom face  → hcomp reduces to the base
[i1]            -- the top face     → hcomp reduces to tube@1
[i0 ∨ i1]      -- union of two faces
[i0 ∧ ¬i1]     -- intersection with a negated face
```

From the test suite:
```
hcomp U1 [i0] ⟨i⟩ U0 U0   -- phi = 0, so hcomp returns the cap U0
hcomp U1 [i1] ⟨i⟩ U0 U0   -- phi = 1, so hcomp returns tube@1 = U0
Glue  U0 [i0] U0            -- phi = 0, so Glue reduces to the base type U0
Glue  U0 [i1] U0            -- phi = 1, so Glue reduces to the fibre U0
```

---

## 6. Term grammar — the big picture

Here is the full grammar in one place. Sections below explain each piece.

```
term  ::=  λx. term                    -- lambda abstraction
        |  ⟨x⟩ term                    -- path abstraction
        |  Π(x : term). term           -- dependent product
        |  app                         -- application spine

app   ::=  atom ( @ atom               -- path application  (left-assoc)
                | atom                 -- function application (left-assoc)
                )*

atom  ::=  U<n>                        -- universe
        |  𝕀                           -- interval pseudo-type
        |  i<n>  |  0  |  1           -- interval literals
        |  Path atom atom atom         -- path type
        |  hcomp atom [iexpr] u atom   -- Kan composition
        |  Glue  atom [iexpr] te       -- Glue type
        |  glue  [iexpr] te atom       -- glue element
        |  unglue [iexpr] te atom      -- unglue element
        |  <name>                      -- variable
        |  ( term )                    -- parenthesised term
```

The key insight is the **two-level split**: binders and application live at the
`term` level; the individual pieces of an application spine (function, arguments)
are `atom`s. This controls which forms need parentheses when nested.

---

## 7. Binders

### Lambda abstraction — `λx. body`

```
λx. body
```

- `λ` followed by a name, then `.`, then the body (which is a full `term`).
- The body extends as far right as possible — `λx. λy. x` is `λx. (λy. x)`,
  not `(λx. λy) x`.

```
λA. λx. x          -- identity function (taking type then value)
λf. λg. λx. f (g x) -- function composition
```

### Dependent product — `Π(x:A). B`

```
Π(x : A). B
```

- `Π` followed by a binder in parentheses `(x : A)`, then `.`, then the result
  type `B`.
- The domain `A` and codomain `B` are full terms.
- Binders nest naturally:

```
-- from the test suite:
Π(A:U0). Π(x:A). A                                -- the type of the identity function
Π(A:U0). Π(B:U0). Π(C:U0). Π(f:Π(x:B).C). Π(g:Π(x:A).B). Π(x:A). C
                                                   -- function composition type
Π(f:Π(x:U0).U0). U1                               -- Pi over a function type
Π(p:Path U1 U0 U0). U1                            -- Pi whose domain is a Path type
```

### Path abstraction — `⟨i⟩ body`

```
⟨i⟩ body
```

- The angle brackets `⟨⟩` (U+27E8 / U+27E9) contain the interval variable name.
- The body is a full `term`.
- Used to introduce an element of a `Path` type: `⟨i⟩ t` has type `Path A t[0] t[1]`
  when `t : A` for all interval values of `i`.

```
⟨i⟩ U0              -- constant path on U0; used as the tube argument in hcomp
```

---

## 8. Application and path application

### Function application

Just juxtapose terms, left-associatively:

```
f x             -- f applied to x
f x y           -- (f x) applied to y
f (g x)         -- f applied to (g x)  — parentheses required here
```

### Path application — `t @ r`

The `@` operator applies a path term to an interval expression:

```
p @ i0          -- evaluate path p at the bottom endpoint
p @ i1          -- evaluate path p at the top endpoint
p @ r           -- evaluate path p at interval variable r
```

Both `@` and plain application are **left-associative** and at the same
precedence level. They can be mixed freely in a spine:

```
f x @ i0 y      -- parsed as  ((f x) @ i0) y
```

---

## 9. Atoms

Atoms are the things that can appear as arguments directly — without any extra
parentheses. Here is each kind:

### Universes — `U<n>`

```
U0    U1    U2    U3    ...
```

`U` followed immediately by one or more decimal digits. `U0` is the smallest
universe; `U1 : U2`, `U0 : U1`, etc.

```
-- from the test suite:
U0
U1
U2
Path U2 U1 U1      -- path between two U1's, living in U2
```

### Interval pseudo-type — `𝕀`

```
𝕀
```

The type of interval expressions. It is not a universe element — it is a
pseudo-type that can only appear in certain positions (e.g. as the type of a
variable in a context, or standalone on a line).

### Interval literals

```
0       -- the bottom endpoint I0
1       -- the top endpoint   I1
i0  i1  i2  ...   -- interval variables
```

These are only recognised as interval literals when **not** followed by more
identifier characters. So `i0` is a literal, but `i0foo` would start a name
lookup for `i0foo`.

### Variables — `<name>`

Any in-scope name resolves to its de Bruijn index at parse time:

```
Π(A:U0). Π(x:A). A     -- here the final A refers to the outer binder
```

If a name is not in scope, the parser fails with `unbound variable: <name>`.

---

## 10. The parenthesisation rule

This is the **most important** practical rule for avoiding parse errors.

`Path`, `hcomp`, `Glue`, `glue`, and `unglue` each take **multiple arguments**.
They can appear at the **head** of an application spine without parentheses, but
when one of them appears as an **argument** to something else, you must
parenthesise it.

```
-- ✅ OK — Path is the head of the whole expression
Path U1 U0 U0

-- ✅ OK — Path is head of the whole line
Path U2 U1 U1

-- ✅ OK — compound Path as argument, wrapped in parens
Path U2 (Path U1 U0 U0) (Path U1 U0 U0)

-- ✅ OK — Pi whose domain is a Path type, parenthesised
Π(p:Path U1 U0 U0). U1

-- ❌ Would fail — Path used as argument without parens
Path U2 Path U1 U0 U0 Path U1 U0 U0
-- parser would read:  Path U2 Path U1   (four atoms)  then fail
```

The same rule applies to `hcomp`, `Glue`, `glue`, and `unglue`:

```
-- ✅ Glue is the head — no parens needed
Glue U0 [i0] U0

-- ✅ Glue as an argument — must be parenthesised
Π(T : (Glue U0 [i0] U0)). U1
```

Inside parentheses, the **full** term grammar is active again, so you can nest
arbitrarily deep.

---

## 11. Cubical constructs in detail

### `Path A u v` — Path type

```
Path  <type>  <start>  <end>
```

All three arguments are atoms (parenthesise if compound). The resulting type
is the type of paths in `A` from `u` to `v`.

```
Path U1 U0 U0           -- a path between U0 and U0 in U1
Path U2 U1 U1           -- a path between U1 and U1 in U2
Path U2 (Path U1 U0 U0) (Path U1 U0 U0)   -- path of paths

-- dependent: A is a variable
Π(A:U1). Π(B:U1). Path U1 A A
```

### `hcomp A [φ] u u0` — Kan composition

```
hcomp  <type>  [<face>]  <tube>  <cap>
```

| Argument | Syntax | What it is |
|---|---|---|
| `A` | atom | The type to compose in |
| `[φ]` | `[` interval expr `]` | The constraint face |
| `u` | bare `⟨i⟩ atom`, `( term )`, or atom | The tube — a path open on one side |
| `u0` | atom | The cap — the base element |

The tube `u` has a special parsing rule: you can write it as a bare path
abstraction `⟨i⟩ atom` without parentheses, but then the body must be a
single atom (not a compound term). For compound tube bodies, use `(⟨i⟩ body)`.

```
hcomp U1 [i0] ⟨i⟩ U0 U0     -- phi=0: reduces to cap U0
hcomp U1 [i1] ⟨i⟩ U0 U0     -- phi=1: reduces to tube@1 = U0
```

**β-reduction behaviour:**
- `φ = 0` (i.e. `[i0]`): result is the cap `u0`
- `φ = 1` (i.e. `[i1]`): result is `u @ 1`, the tube evaluated at 1

### `Glue A [φ] T` — Glue type formation

```
Glue  <base type>  [<face>]  <fibre type or equiv>
```

| Argument | Syntax | What it is |
|---|---|---|
| `A` | atom | The base type |
| `[φ]` | `[` interval expr `]` | The constraint face |
| `T` | `( term )` or atom | The fibre / equivalence data |

```
Glue U0 [i0] U0    -- phi=0: reduces to the base type U0
Glue U0 [i1] U0    -- phi=1: reduces to the fibre U0
```

**β-reduction behaviour:**
- `φ = 0`: `Glue A [0] T` reduces to `A`
- `φ = 1`: `Glue A [1] T` reduces to `T`

### `glue [φ] t a` — glue element introduction

```
glue  [<face>]  <partial element>  <base element>
```

Introduces an element of a Glue type. `t` lives in the fibre and `a` lives in
the base type. When `φ = 1` the result is `t`; when `φ = 0` the result is `a`.

### `unglue [φ] T g` — unglue element elimination

```
unglue  [<face>]  <fibre type>  <glue element>
```

Projects out of a Glue type, returning an element of the base type.
When `φ = 1` applies the equivalence; when `φ = 0` returns `g` unchanged.

---

## 12. Common mistakes

### Forgetting square brackets around the face

```
-- ❌ Wrong
hcomp U1 i0 ⟨i⟩ U0 U0

-- ✅ Correct
hcomp U1 [i0] ⟨i⟩ U0 U0
```

The face argument of `hcomp`, `Glue`, `glue`, and `unglue` is **always** written
inside `[…]`.

### Forgetting to parenthesise compound arguments

```
-- ❌ Wrong — parser reads Path as taking atoms Path, U1, U0, then sees 0 leftover
Path U2 Path U1 U0 U0 Path U1 U0 U0

-- ✅ Correct
Path U2 (Path U1 U0 U0) (Path U1 U0 U0)
```

### Confusing interval literals with names

```
-- i0 by itself is an interval literal — it has type 𝕀
i0

-- i0foo is looked up as a name — make sure it's in scope or you get
-- "unbound variable: i0foo"
```

### Using a plain name where a keyword is expected

```
-- "Glue" with capital G is the type-formation keyword
Glue U0 [i0] U0

-- "glue" with lowercase g is the element-introduction keyword
glue [i1] t a

-- These are case-sensitive — swapping them is a parse error
```

### Writing nested binders in Pi without re-wrapping

```
-- ✅ Correct — each Π has its own (x:A). part
Π(A:U0). Π(x:A). A

-- ❌ Wrong — Π(A:U0)(x:A) is not valid syntax
Π(A:U0)(x:A). A
```

### Tube body in hcomp consuming the cap

If you write a bare `⟨i⟩ <term>` as the tube, the body is **one atom** only.
For a compound body, use parentheses:

```
-- ✅ Body is the single atom U0; u0 is the next atom U0
hcomp U1 [i0] ⟨i⟩ U0 U0

-- ✅ Compound tube body wrapped in parens; u0 is still U0
hcomp U1 [i0] (⟨i⟩ Path U1 U0 U0) U0
```

---

*That covers everything the parser accepts. When in doubt, add parentheses —
they never hurt and the inner term always gets the full grammar.*