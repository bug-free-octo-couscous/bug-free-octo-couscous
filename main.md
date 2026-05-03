```haskell
import qualified Data.Set as Set

-- 1. Data Definition
type Name = String
type Index = Int

data Term
    = Var Index -- variable use indecs De bruijin indecs
    | App Term Term --apply function
    | Lam Name Term Term  -- Name is a hint for printing
    | Pi  Name Term Term  --Pi type 
    | Kind                -- (*)
    | Box                 -- (□)
    deriving (Eq)

instance Show Term where
    show (Var i)     = show i
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"
    show Box         = "□"

-- 2. De Bruijn Shifting and Substitution
-- shift d c t: increments all indices in t that are >= c by d
shift :: Int -> Int -> Term -> Term
shift d c (Var i)     = if i >= c then Var (i + d) else Var i
shift d c (App m n)   = App (shift d c m) (shift d c n)
shift d c (Lam x t e) = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)  = Pi x (shift d c t) (shift d (c + 1) b)
shift _ _ Kind        = Kind
shift _ _ Box         = Box

-- substitute j n m: replaces index j in m with term n
substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) = 
    Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  = 
    Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute _ _ Kind = Kind
substitute _ _ Box  = Box

-- 3. Evaluation / Normalization
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        -- Beta reduction: shift -1 because the Lam binder is removed
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

-- 4. Type Checking Logic
-- Context is now a list of types; index i refers to the i-th element.
type Context = [Term]

typeOf :: Context -> Term -> Either String Term
typeOf _ Box = Left "Type Error: Box is the top of the hierarchy"
typeOf _ Kind = Right Box

typeOf ctx (Var i) 
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    sA <- typeOf ctx a
    sB <- typeOf (a : ctx) b
    if (sA == Kind || sA == Box) && (sB == Kind || sB == Box)
        then Right sB 
        else Left "Type Error: Pi components must be Types or Kinds"

typeOf ctx (Lam x a e) = do
    _ <- typeOf ctx a 
    b <- typeOf (a : ctx) e
    return (Pi x a b)

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b -> 
            if reduce a == reduce tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left "Type mismatch: Argument type does not match Pi domain"
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function type"

-- 5. Main Execution
main :: IO ()
main = do
    putStrLn "--- De Bruijn Index Type System ---"

    -- We'll put "Bool" in our context as index 0.
    -- Context: [Kind] (Meaning index 0 has type Kind)
    let ctx = [Kind] 

    -- Example 1: Polymorphic Identity λA:*. λx:A. x
    -- Nested binders: A is index 1, x is index 0.
    let polyId = Lam "A" Kind (Lam "x" (Var 0) (Var 0))
    
    putStrLn $ "Term: " ++ show polyId
    case typeOf ctx polyId of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e

    -- Example 2: Applying PolyId to index 0 (which is our "Bool")
    let appBool = App polyId (Var 0)
    putStrLn $ "\nApplying to Var 0: " ++ show appBool
    case typeOf ctx appBool of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e
```
This Haskell implementation demonstrates a **Pure Type System (PTS)**—specifically a variant of the **Lambda Cube** (like the Calculus of Constructions)—using **De Bruijn Indices** for variable management.

Below is a breakdown of the core concepts and how the code functions.

---

## 1. Data Definition: The Syntax
The `Term` data type represents the building blocks of the language. Unlike standard lambda calculus, this system merges "terms" and "types" into a single structure.

*   **`Var Index`**: Uses **De Bruijn Indices** (integers) instead of names. `0` refers to the innermost binder, `1` to the next, and so on. This eliminates the "variable capture" problem during substitution.
*   **`Pi Name Term Term`**: Represents Dependent Types ($\Pi$-types). If the second `Term` doesn't use the bound variable, this acts like a standard function arrow ($A \to B$).
*   **`Kind (*)` and `Box (□)`**: These are the "Sorts."
    *   `Kind` is the type of types (like `Int` or `Bool`).
    *   `Box` is the type of `Kind`.

---

## 2. De Bruijn Index Management
Managing variables without names requires two helper operations: **Shifting** and **Substitution**.

### Shifting (`shift`)
When you move a term underneath a new binder (a `Lam` or `Pi`), its free variables must be incremented so they still point to the correct "outside" binders.
*   **`d`**: The amount to add.
*   **`c`**: The cutoff (only indices $\ge c$ are free variables that need shifting).

### Substitution (`substitute`)
This replaces a variable (index `j`) with a new term `n`. 
> **Note:** In the `Lam` and `Pi` cases, notice the `shift 1 0 n`. This is because as we descend into a binder, the context grows, so the free variables inside the term we are inserting must be adjusted.

---

## 3. Evaluation (Normalization)
The `reduce` function performs **$\beta$-reduction**.

```haskell
reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
```
When applying a function $(\lambda x. e)n$:
1.  We prepare $n$ by shifting it up.
2.  We substitute it into $e$ at index $0$.
3.  We **shift the whole result by -1**. This is crucial: since the $\lambda$ binder is now gone, all remaining free variables in $e$ must "move down" one level to stay correct.

---

## 4. The Type System (`typeOf`)
This is the heart of the logic. It follows the rules of the Lambda Cube.

| Rule | Explanation |
| :--- | :--- |
| **Sorts** | `Kind` has type `Box`. `Box` is the "top" and has no type. |
| **Variables** | Look up the type in the `ctx`. We shift the retrieved type because the variable is $i$ levels deep in the stack. |
| **Pi-Types** | A $\Pi$-type is valid only if its components are valid sorts (Types or Kinds). |
| **Abstraction** | To type check $\lambda x:A. e$, we assume $x$ has type $A$ and check the body $e$. The result is a $\Pi$-type. |
| **Application** | If $m$ is a function $(\Pi x:A. B)$ and $n$ has type $A$, the result is $B$ with $n$ substituted in. |

---

## 5. Walkthrough: Polymorphic Identity
In the `main` function, the code defines:
`λA:*. λx:A. x` $\rightarrow$ `Lam "A" Kind (Lam "x" (Var 0) (Var 0))`

1.  **Outer Lam ("A")**: Binds index 0 as `Kind`.
2.  **Inner Lam ("x")**: Binds a new index 0 as type `A` (which is now index 1).
3.  **Variable (Var 0)**: Refers to `x`.

**The result of `typeOf`**:
`ΠA:*. Πx:A. A`

### Why use De Bruijn Indices?
While they are harder for humans to read (e.g., `Var 0` vs `x`), they are perfect for computers because:
*   **Alpha-equivalence is trivial**: `λx.x` and `λy.y` both become `Lam 0`.
*   **No Name Clashes**: You never have to worry about "renaming" variables to avoid accidentally shadowing a global variable.

---

### Suggestions for Extension
If you want to make this code more powerful, you could:
1.  **Add a Parser**: Convert strings like `\A:*. \x:A. x` into the `Term` data type.
2.  **Add Constants**: Add `Nat` or `String` as primitive types.
3.  **Pretty Printer**: Write a function that converts De Bruijn indices back into human-readable names using the `Name` hints provided in the constructors.