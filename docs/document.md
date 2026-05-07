# Cubical Lambda — Grammar Guide

This guide explains the full surface syntax of Cubical Lambda, with examples
drawn from the test suite. After reading this you should be able to write any
well-formed term without hitting a parse error.

---

## Table of Contents

1. [Quick-start cheatsheet](#1-quick-start-cheatsheet)
2. [File format and statements](#2-file-format)
3. [Lexical basics — names, keywords, whitespace](#3-lexical-basics)
4. [Unicode symbols you need](#4-unicode-symbols)
5. [Interval expressions](#5-interval-expressions)
6. [Term grammar — the big picture](#6-term-grammar)
7. [Binders — λ, Π, ⟨⟩](#7-binders)
8. [Application and path application](#8-application-and-path-application)
9. [Atoms — the building blocks](#9-atoms)
10. [The parenthesisation rule](#10-the-parenthesisation-rule)
11. [Cubical constructs in detail](#11-cubical-constructs-in-detail)
12. [Equivalences and univalence](#12-equivalences-and-univalence)
13. [Common mistakes and how to fix them](#13-common-mistakes)

---

## 1. Quick-start cheatsheet

| What you want to write | Syntax |
|---|---|
| Define a name (inferred type) | `def x = e` |
| Define a name (explicit type) | `def x : T = e` |
| Check a term without binding | `check label : T = e` |
| Infer the type of a term | `<term>` (bare, no keyword) |
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
| Glue type | `Glue A [φ] e` |
| Glue element | `glue [φ] t a` |
| Unglue element | `unglue [φ] e g` |
| Equivalence type | `Equiv A B` |
| Build an equivalence | `mkEquiv A B f g η ε` |
| Apply forward map | `equivFwd e x` |
| Univalence map | `ua e` |
| Transport along a path | `transport p x` |
| Parenthesise anything | `( … )` |

---

## 2. File format and statements

The CLI reads your source file line by line. Each non-blank, non-comment line is
one **statement**. Statements can define names, check terms, or infer the type of
a bare term. Crucially, definitions **persist** — every line sees the names
defined on all previous lines.

### Statement kinds

#### `def x : T = e` — define with explicit type

Checks that `e` has type `T`, then binds the name `x` to `e` in all subsequent
lines. The type annotation is mandatory when the term cannot be inferred on its
own (e.g. a bare lambda).

```
def myBool : U0 = U0
def id : Π(x:U0). U0 = λx. x
```

#### `def x = e` — define with inferred type

Infers the type of `e`, then binds `x`. Use this when the type is obvious.

```
def U = U0          -- x = U0, type inferred as U1
def idId = id id    -- uses previously defined id
```

#### `check label : T = e` — check without binding

Verifies `e : T` and reports success or failure, but does **not** add anything to
the environment. Useful for assertions and tests.

```
check myLemma : Path U1 U0 U0 = ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))
```

#### `<term>` — bare term (infer only)

A line that is none of the above is treated as a bare term whose type is inferred
and printed. Nothing is added to the environment.

```
U0                          -- infers U1
Π(A:U0). Π(x:A). A         -- infers U1
```

### Comments and blank lines

```
-- This is a comment and is ignored entirely.

-- Blank lines are also ignored.

def A = U0          -- definitions accumulate across lines
def B = U0
Equiv A B           -- A and B are in scope here
```

### Scoping rules

- Names are in scope from the line **after** the `def` that introduces them.
- A `def` on line *n* can reference any name defined on lines 1 … *n*−1.
- `check` and bare terms have read-only access to the environment.
- There is no shadowing protection — redefining a name silently replaces it.

### Why not one term per line?

The previous format required each term to be self-contained on a single line.
This made it impossible to build up complex types incrementally. The statement
format removes that constraint: you can define helper types and functions once
and reuse them across many subsequent lines.

```
-- Old style — everything inline, hard to read:
transport (ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))) U0

-- New style — build up in named steps:
def idEquiv = mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
def uaPath  = ua idEquiv
transport uaPath U0
```

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
def   check
Path   hcomp   Glue   glue   unglue   Equiv   mkEquiv   equivFwd   ua   transport
```

A keyword is only recognised when it is **not immediately followed** by a letter,
digit, or underscore. So `Glue` is the keyword, but `GlueExtra` would be parsed
as a plain name (if it were in scope). Likewise `uaβ` would be a plain name,
not the `ua` keyword.

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
-- Top-level statements (one per line in a source file)
stmt  ::=  def <name> : term = term      -- define with explicit type
        |  def <name> = term             -- define with inferred type
        |  check <name> : term = term    -- check without binding
        |  term                          -- bare term: infer and print type

-- Terms
term  ::=  λx. term                         -- lambda abstraction
        |  ⟨x⟩ term                         -- path abstraction
        |  Π(x : term). term                -- dependent product
        |  app                              -- application spine

app   ::=  atom ( @ atom                    -- path application  (left-assoc)
                | atom                      -- function application (left-assoc)
                )*

atom  ::=  U<n>                             -- universe
        |  𝕀                                -- interval pseudo-type
        |  i<n>  |  0  |  1                -- interval literals
        |  Path atom atom atom              -- path type
        |  hcomp atom [iexpr] u atom        -- Kan composition
        |  Glue  atom [iexpr] te            -- Glue type
        |  glue  [iexpr] te atom            -- glue element
        |  unglue [iexpr] te atom           -- unglue element
        |  Equiv atom atom                  -- equivalence type
        |  mkEquiv atom atom te te te te    -- build an equivalence
        |  equivFwd te atom                 -- apply forward map
        |  ua te                            -- univalence map
        |  transport te atom                -- transport along a path
        |  <name>                           -- variable (local or global)
        |  ( term )                         -- parenthesised term
```

where `te` means: `( term )` or `atom` (parentheses required for compound terms).

The key insight is the **two-level split**: binders and application live at the
`term` level; the individual pieces of an application spine (function, arguments)
are `atom`s. This controls which forms need parentheses when nested.

Names appearing as atoms are resolved first against local binders (lambda, Pi,
path abstraction), then against the accumulated global environment from prior
`def` statements.

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
Π(e:Equiv U0 U0). Path U1 U0 U0                   -- Pi whose domain is an Equiv type
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

A name resolves to a value at parse time. The resolver checks first against
**local binders** (lambda, Pi, path abstraction arguments), then against the
**global environment** built up from preceding `def` statements.

```
Π(A:U0). Π(x:A). A     -- the final A refers to the outer Π binder

def Nat = U0            -- Nat is now a global name
Π(n:Nat). Nat           -- Nat resolves to U0 from the global env
```

If a name is not in scope either locally or globally, the parser fails with
`unbound variable: <name>`.

---

## 10. The parenthesisation rule

This is the **most important** practical rule for avoiding parse errors.

`Path`, `hcomp`, `Glue`, `glue`, `unglue`, `Equiv`, `mkEquiv`, `equivFwd`,
`ua`, and `transport` each take **multiple arguments**. They can appear at the
**head** of an application spine without parentheses, but when one of them
appears as an **argument** to something else, you must parenthesise it.

```
-- ✅ OK — Path is the head of the whole expression
Path U1 U0 U0

-- ✅ OK — compound Path as argument, wrapped in parens
Path U2 (Path U1 U0 U0) (Path U1 U0 U0)

-- ✅ OK — Pi whose domain is a Path type, parenthesised
Π(p:Path U1 U0 U0). U1

-- ❌ Would fail — Path used as argument without parens
Path U2 Path U1 U0 U0 Path U1 U0 U0
-- parser would read:  Path U2 Path U1   (four atoms)  then fail
```

The same rule applies to the equivalence and univalence constructs:

```
-- ✅ Equiv is the head — no parens needed
Equiv U0 U0

-- ✅ Equiv as an argument — must be parenthesised
Π(e : (Equiv U0 U0)). Path U1 U0 U0

-- ✅ ua is the head — no parens needed
ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))

-- ✅ ua result as an argument — must be parenthesised
transport (ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))) U0
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

### `Glue A [φ] e` — Glue type formation

```
Glue  <base type>  [<face>]  <equivalence or fibre>
```

| Argument | Syntax | What it is |
|---|---|---|
| `A` | atom | The base type |
| `[φ]` | `[` interval expr `]` | The constraint face |
| `e` | `( term )` or atom | An `Equiv T A` giving the fibre type and map |

The third argument is typically a `mkEquiv` term (see [Section 12](#12-equivalences-and-univalence)).
For the β-rules to fire correctly it must reduce to an `Equiv T A`.

```
Glue U0 [i0] e    -- phi=0: reduces to the base type U0
Glue U0 [i1] e    -- phi=1: reduces to dom(e), the domain of the equivalence
```

**β-reduction behaviour:**
- `φ = 0`: `Glue A [0] e` reduces to `A`
- `φ = 1`: `Glue A [1] e` reduces to the domain type of `e`

> **Change from previous versions:** The third argument was previously an
> untyped fibre `T`. It is now an equivalence `e : Equiv T A`. The β-rule
> for `φ = 1` now correctly extracts the domain of `e` rather than reducing
> to the raw `T` term.

### `glue [φ] t a` — glue element introduction

```
glue  [<face>]  <partial element>  <base element>
```

Introduces an element of a Glue type. `t` lives in the domain of the
equivalence (the fibre type) and `a` lives in the base type `A`.
When `φ = 1` the result is `t`; when `φ = 0` the result is `a`.

### `unglue [φ] e g` — unglue element elimination

```
unglue  [<face>]  <equivalence>  <glue element>
```

Projects out of a Glue type, returning an element of the base type.

**β-reduction behaviour:**
- `φ = 1`: applies the **forward map** of equivalence `e` to `g`, i.e. `equivFwd e g`
- `φ = 0`: returns `g` unchanged (it already lives in `A`)

> **Change from previous versions:** When `φ = 1`, `unglue` previously returned
> `g` unchanged (identity). It now correctly applies the equivalence's forward
> map. This is the coherence condition that makes Glue/unglue a proper
> round-trip.

---

## 12. Equivalences and univalence

This section covers the five new constructs that implement the univalence axiom.

### `Equiv A B` — equivalence type

```
Equiv  <domain>  <codomain>
```

The type of equivalences from `A` to `B`. Both arguments are atoms.

```
Equiv U0 U0          -- type of self-equivalences of U0; lives in U1
Equiv U0 U1          -- equivalences from U0 to U1; lives in U2
Π(e : (Equiv U0 U0)). Path U1 U0 U0    -- Pi over an equivalence
```

**Typing rule:** If `A : U_n` and `B : U_n` then `Equiv A B : U_n`.

### `mkEquiv A B f g η ε` — building an equivalence

```
mkEquiv  <A>  <B>  <f>  <g>  <η>  <ε>
```

| Argument | Type | Role |
|---|---|---|
| `A` | atom | Domain type |
| `B` | atom | Codomain type |
| `f` | `( term )` or atom | Forward map `f : A → B` |
| `g` | `( term )` or atom | Backward map `g : B → A` |
| `η` | `( term )` or atom | Left homotopy `η : Π(a:A). Path A a (g (f a))` |
| `ε` | `( term )` or atom | Right homotopy `ε : Π(b:B). Path B (f (g b)) b` |

The checker verifies that `f`, `g`, `η`, and `ε` all have the correct dependent
types. The result has type `Equiv A B`.

**The identity equivalence on `A`** (where `f = g = λx.x` and both homotopies
are constant paths):

```
mkEquiv A A (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
```

As a closed term at `A = U0`:

```
mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
```

Because `f`, `g`, `η`, and `ε` are almost always compound lambda terms, they
nearly always need to be wrapped in parentheses when written inline.

### `equivFwd e x` — applying the forward map

```
equivFwd  <equiv>  <element>
```

Applies the forward map of equivalence `e : Equiv A B` to an element `x : A`,
producing a result of type `B`.

```
equivFwd (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)) U0
-- reduces to (λx. x) U0  =  U0
```

**β-rule:** `equivFwd (mkEquiv A B f g η ε) x  ≡  f x`

The first argument `e` is a `( term )` or atom; the second `x` is an atom.
Because `mkEquiv` takes six arguments it almost always needs parentheses:

```
-- ✅ Correct
equivFwd (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)) U0

-- ❌ Wrong — parser will try to treat mkEquiv as the atom for equivFwd,
--    then fail because mkEquiv expects more arguments
equivFwd mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b) U0
```

### `ua e` — the univalence map

```
ua  <equiv>
```

Converts an equivalence `e : Equiv A B` into a path `ua e : Path U_n A B` in
the universe. This is the **univalence axiom** — the claim that equivalent types
are identical (as a path in the universe).

```
ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))
-- : Path U1 U0 U0
```

**Typing rule:** If `e : Equiv A B` and `A : U_n` then `ua e : Path U_n A B`.

`ua` itself does not reduce further — it is a constructor. Its computational
content is exposed via `transport` (see uaβ below).

The argument is a `( term )` or atom. Since the argument is typically a `mkEquiv`
application it almost always needs parentheses.

### `transport p x` — transporting along a path

```
transport  <path>  <element>
```

Given a path `p : Path U_n A B` in a universe and an element `x : A`, produces
an element `transport p x : B` by coercing `x` along `p`.

```
transport (ua e) x      -- transport along a univalence path
transport (⟨i⟩ U0) x   -- transport along a constant path — reduces to x
```

**β-rules:**

| Condition | Reduction |
|---|---|
| `p = ua e` | `transport (ua e) x  ≡  equivFwd e x` &nbsp;&nbsp; **(uaβ — the key univalence computation)** |
| `p = ⟨i⟩ A` and body is constant | `transport (⟨i⟩ A) x  ≡  x` |

The uaβ rule is the computational heart of univalence: transporting along a
`ua` path *computes* by applying the forward map of the equivalence.

```
-- Suppose e = mkEquiv U0 U0 (λx. x) ...
-- Then:
transport (ua e) U0
  ≡  equivFwd e U0        -- by uaβ
  ≡  (λx. x) U0           -- by equivFwd β
  ≡  U0                   -- by λ β
```

The first argument `p` is a `( term )` or atom; the second `x` is an atom.
As with `ua` and `equivFwd`, the path argument is usually compound and needs
parentheses:

```
-- ✅ Correct
transport (ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))) U0

-- ❌ Wrong — ua is seen as an atom, then mkEquiv ... is extra leftover
transport ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)) U0
```

### Putting it together — a worked univalence example

```
-- Step 1: build the identity equivalence on U0
mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
-- : Equiv U0 U0

-- Step 2: turn it into a path in U1
ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))
-- : Path U1 U0 U0

-- Step 3: transport U0 along that path — should give back U0
transport (ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))) U0
-- reduces by uaβ to:  equivFwd (mkEquiv ...) U0
-- reduces by equivFwd β to:  (λx. x) U0
-- reduces by λ β to:  U0
```

---

## 13. Common mistakes

### Using a name before it is defined

Definitions only become available on the line **after** the `def` that introduces
them. Referring to a name on the same line as its `def` is not allowed.

```
-- ❌ Wrong — myType is not yet in scope on its own def line
def myType : myType = U0

-- ✅ Correct — define first, use after
def myType = U0
def myAlias : myType = U0   -- myType is in scope here
```

### Forgetting `def` makes a name globally available

A bare term on a line infers its type but **does not bind a name**. If you want
to reuse a term on a later line, you must use `def`.

```
-- ❌ This does NOT make idEquiv available later
mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)

-- ✅ This does
def idEquiv = mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
transport (ua idEquiv) U0    -- idEquiv is in scope here
```

### Omitting the type annotation on a bare lambda

The type checker cannot infer the type of a lambda without a hint. Always
provide `: T` in the `def` header, or embed the lambda inside a typed expression.

```
-- ❌ Wrong — cannot infer type of λx. x
def myId = λx. x

-- ✅ Correct — type given explicitly
def myId : Π(x:U0). U0 = λx. x
```

### Confusing `def` and `check`

`check label : T = e` verifies `e : T` but does **not** add `label` to the
environment. If you need to refer to the value later, use `def` instead.

```
check myLemma : Path U1 U0 U0 = ua idEquiv   -- OK for testing
myLemma                                        -- ❌ unbound — check didn't bind it

def myLemma : Path U1 U0 U0 = ua idEquiv     -- ✅ now it's in scope
myLemma                                        -- ✅ works
```

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

This applies equally to `Equiv`, `ua`, `mkEquiv`, `equivFwd`, and `transport`:

```
-- ❌ Wrong — ua is an atom here; mkEquiv ... becomes leftover tokens
transport ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)) U0

-- ✅ Correct
transport (ua (mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b))) U0
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
Glue U0 [i0] e

-- "glue" with lowercase g is the element-introduction keyword
glue [i1] t a

-- "Equiv" with capital E is the type keyword
Equiv U0 U0

-- "equivFwd" is the elimination keyword (camelCase, all one word)
equivFwd e x

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

### Forgetting that mkEquiv needs six arguments

`mkEquiv` takes `A B f g η ε` — six arguments total. A common mistake is to
omit one of the homotopies or to confuse the order. The checker will report a
type mismatch or `CannotInfer` if the count is wrong.

```
-- ✅ All six arguments present
mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a) (λb. ⟨i⟩ b)
--       A    B    f             g             η              ε

-- ❌ Missing ε — parser will try to read the next token as ε and likely fail
mkEquiv U0 U0 (λx. x) (λx. x) (λa. ⟨i⟩ a)
```

---

*When in doubt, add parentheses — they never hurt and the inner term always gets the full grammar.*