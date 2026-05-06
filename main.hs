import CubicalLambda
--------------------------------------------------------------------------------
-- Main
-- i need parser
--------------------------------------------------------------------------------

main :: IO ()
main = do
    demoEval
    demoTypeCheck
    demoKan
    demoGlue

-- demos -----------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Eval Demo
--------------------------------------------------------------------------------

demoEval :: IO ()
demoEval = do
    putStrLn "=== Cubical Lambda Calculus with Path Types ==="

    -- 1. Identity function (Standard Pi Type)
    -- Π(A:U0). Π(x:A). A
    -- In de Bruijn: outer binder = 1, inner binder = 0
    let idType = TPi "A" (TUniv 0) (TPi "x" (TVar 0) (TVar 1))
    -- λA. λx. x  — x is de Bruijn 0
    let idTerm = TAbs "A" (TAbs "x" (TVar 0))

    putStrLn $ "\nIdentity Type: " ++ show idType
    putStrLn $ "Identity Term: " ++ show idTerm

    -- 2. Reflexivity (Path Type)
    -- refl : Π(A:U0). Π(x:A). Path A x x
    -- refl = λA. λx. ⟨i⟩ x
    -- Indices inside PLam body: x=1 (past PLam binder), A=2
    let refl = TAbs "A" (TAbs "x" (PLam "i" (TVar 1)))
    putStrLn $ "\nReflexivity (refl): " ++ show refl

    -- 3. Path Application
    -- (refl U0 T) @ 0  where T is a free variable we put in context
    -- We use TVar 0 to stand for the free variable T
    let testPath = PApp (TApp (TApp refl (TUniv 0)) (TVar 0)) (TInterval I0)
    putStrLn $ "\nEvaluating (refl U0 T) @ 0:"
    putStrLn $ "Result: " ++ show (eval testPath)

    -- 4. De Morgan in the Interval (Normalized inside a Path)
    let deMorganLHS = Neg (Join (IVar 0) (IVar 1))
    let deMorganRHS = Meet (Neg (IVar 0)) (Neg (IVar 1))
    let pathDeMorgan = TPath (TUniv 0) (TInterval deMorganLHS) (TInterval deMorganRHS)

    putStrLn $ "\nNormalized De Morgan Interval in Type:"
    putStrLn $ "Raw:        " ++ show pathDeMorgan
    putStrLn $ "Normalized: " ++ show (eval pathDeMorgan)

    -- 5. Symmetry (Function that flips a path)
    -- sym = λA. λx. λy. λp. ⟨i⟩ p @ ¬i
    -- Indices at PLam body depth (4 binders + 1 PLam = depth 5):
    --   i   = TVar 0  (PLam binder)
    --   p   = TVar 1  (4th λ)
    --   y   = TVar 2  (3rd λ)
    --   x   = TVar 3  (2nd λ)
    --   A   = TVar 4  (1st λ)
    let sym = TAbs "A" (TAbs "x" (TAbs "y"
                (TAbs "p" (PLam "i"
                    (PApp (TVar 1) (TInterval (Neg (IVar 0))))))))
    putStrLn $ "\nSymmetry term: " ++ show sym

-- ---------------------------------------------------------------------------
-- Type-checker demo
-- ---------------------------------------------------------------------------

demoTypeCheck :: IO ()
demoTypeCheck = do
    putStrLn "\n=== Bidirectional Type Checker ==="

    -- ── 1. Universe levels ──────────────────────────────────────────────────
    putStrLn "\n── Universe Levels ─────────────────────────────────────────"
    reportInfer "U0"       (TUniv 0)
    reportInfer "U1"       (TUniv 1)
    reportInfer "U0 : U1"  (TUniv 0)   -- should give U1

    -- ── 2. Identity function ─────────────────────────────────────────────────
    --   id : Π(A:U0). Π(x:A). A
    --   id = λA. λx. x
    --   De Bruijn:  Π(U0). Π(0). 1    (A is 1 past the x-binder, x is 0)
    putStrLn "\n── Identity Function ───────────────────────────────────────"
    let idTy = TPi "A" (TUniv 0) (TPi "x" (TVar 0) (TVar 1))
    let idTm = TAbs "A" (TAbs "x" (TVar 0))
    reportCheck "identity" idTm idTy

    -- ── 3. Reflexivity ───────────────────────────────────────────────────────
    --   refl : Π(A:U0). Π(x:A). Path A x x
    --   refl = λA. λx. ⟨i⟩ x
    --   Inside PLam (depth 3): x = TVar 1, A = TVar 2
    putStrLn "\n── Reflexivity ─────────────────────────────────────────────"
    let reflTy = TPi "A" (TUniv 0)
                     (TPi "x" (TVar 0)
                          (TPath (TVar 1) (TVar 0) (TVar 0)))
    let reflTm = TAbs "A" (TAbs "x" (PLam "i" (TVar 1)))
    reportCheck "refl" reflTm reflTy 

    -- ── 4. Function composition ──────────────────────────────────────────────
    --   comp : Π(A B C : U0). (A → B) → (B → C) → A → C
    --   comp = λA B C f g x. g (f x)
    --   Depth map at body (6 binders):
    --     x=0, g=1, f=2, C=3, B=4, A=5
    putStrLn "\n── Function Composition ────────────────────────────────────"
    let arr a b = TPi "_" a b       -- non-dependent arrow A → B
    -- Note: in arr the bound var is unused so we shift:
    --   A→B at depth d means: Π(_:A). shift 1 0 B  (B's vars don't refer to _)
    let compTy =
            TPi "A" (TUniv 0) $          -- A=0 inside
            TPi "B" (TUniv 0) $          -- B=0, A=1
            TPi "C" (TUniv 0) $          -- C=0, B=1, A=2
            TPi "f" (TPi "_" (TVar 2) (TVar 2)) $   -- f : A→B  (A=2,B=2 after shift)
            TPi "g" (TPi "_" (TVar 2) (TVar 2)) $   -- g : B→C
            TPi "x" (TVar 4) $           -- x : A  (A is now 4 deep)
            TVar 5                       -- return type C (now at 5)
    let compTm =
            TAbs "A" $ TAbs "B" $ TAbs "C" $
            TAbs "f" $ TAbs "g" $ TAbs "x" $
            TApp (TVar 1) (TApp (TVar 2) (TVar 0))
    reportCheck "compose" compTm compTy

    -- ── 5. Constant path in context ──────────────────────────────────────────
    --   In context [x:A, A:U0], check ⟨i⟩ x : Path A x x
    --   Context stack (index 0 = top):  [("x", TVar 0), ("A", TUniv 0)]
    --   But we build it with extendCtx so:
    --     ctx = [("x", TVar 0 shifted), ("A", TUniv 0)]
    --   We use a direct context list here with pre-shifted types.
    --   At depth 0: A is index 1, x is index 0.
    putStrLn "\n── Constant Path in Context ────────────────────────────────"
    let ctxWithAx = [("x", TVar 0), ("A", TUniv 0)]
      -- x : TVar 0  means "x has type = de Bruijn 0 in the context where x was added"
      -- After lookupCtx 0 (x) → shift 1 0 (TVar 0) = TVar 1, which is A. Correct.
    -- ⟨i⟩ x  where x is de Bruijn 1 inside PLam (0=i, 1=x, 2=A)
    let constPath   = PLam "i" (TVar 1)
    -- Path A x x  where A=TVar 1, x=TVar 0 (at outer depth, ctx has 2 entries)
    let constPathTy = TPath (TVar 1) (TVar 0) (TVar 0)
    case check ctxWithAx constPath constPathTy of
        Right () -> putStrLn $
            "  ✓  ⟨i⟩ x : Path A x x   (in context A:U0, x:A)"
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── 6. Path application ───────────────────────────────────────────────────
    --   ctx: [("p", Path U1 (TVar 1) (TVar 1)), ("T", TUniv 0)]
    --   p @ 0  and  p @ 1  both have type U0.
    putStrLn "\n── Path Application ────────────────────────────────────────"
    let ctxP = [ ("p", TPath (TUniv 0) (TVar 0) (TVar 0))
               , ("T", TUniv 0) ]
    -- p is de Bruijn 0 in this 2-entry context
    let app0 = PApp (TVar 0) (TInterval I0)
    let app1 = PApp (TVar 0) (TInterval I1)
    mapM_ (\(lbl, t) ->
        case infer ctxP t of
            Right ty -> putStrLn $
                "  ✓  " ++ lbl ++ "  : " ++ show ty
            Left err -> putStrLn $ "  ✗  " ++ lbl ++ ": " ++ show err)
        [ ("p @ 0", app0), ("p @ 1", app1) ]

    -- ── 7. Ill-typed: applying non-function ───────────────────────────────────
    putStrLn "\n── Ill-typed Examples ──────────────────────────────────────"
    reportInfer "U0 U0 (expected error)" (TApp (TUniv 0) (TUniv 0))

    let badCheck = check [] (PLam "i" (TVar 0)) (TUniv 0)
    case badCheck of
        Left err -> putStrLn $ "  ✓  ⟨i⟩ i : U0 correctly rejected:\n" ++ show err
        Right () -> putStrLn "  ✗  Should have been rejected!"

    -- ── 8. Church booleans ────────────────────────────────────────────────────
    --   Bool := Π(A:U0). A → A → A
    --   true := λA. λt. λf. t    (t = de Bruijn 1)
    --   false := λA. λt. λf. f   (f = de Bruijn 0)
    putStrLn "\n── Church Booleans ─────────────────────────────────────────"
    let boolTy = TPi "A" (TUniv 0)
                    (TPi "t" (TVar 0)
                        (TPi "f" (TVar 1) (TVar 2)))
    let trueTm  = TAbs "A" (TAbs "t" (TAbs "f" (TVar 1)))
    let falseTm = TAbs "A" (TAbs "t" (TAbs "f" (TVar 0)))
    reportCheck "true"  trueTm  boolTy
    reportCheck "false" falseTm boolTy

    -- ── 9. Pi type itself is well-typed ──────────────────────────────────────
    putStrLn "\n── Π Type Formation ────────────────────────────────────────"
    let bigPi = TPi "x" (TUniv 0) (TUniv 0)
    reportInfer "Π(x:U0).U0" bigPi

    -- ── 10. Path type is well-typed ───────────────────────────────────────────
    putStrLn "\n── Path Type Formation ─────────────────────────────────────"
    -- In context [x:A, A:U0]: A=TVar 1, x=TVar 0
    let pathType = TPath (TVar 1) (TVar 0) (TVar 0)
    let ctxAx = [("x", TVar 0), ("A", TUniv 0)]
    case infer ctxAx pathType of
        Right ty -> putStrLn $
            "  ✓  Path A x x  (in context A:U0, x:A)\n       : " ++ show ty
        Left err -> putStrLn $ "  ✗  " ++ show err

--------------------------------------------------------------------------------
-- Kan Composition Demo
--------------------------------------------------------------------------------

demoKan :: IO ()
demoKan = do
    putStrLn "\n=== Kan Composition (hcomp) ==="

    -- ── β-rule ⊤ ──────────────────────────────────────────────────────────────
    -- hcomp A ⊤ (⟨i⟩ t) u₀ where A,t,u0 are free (TVar 0,1,2 in open ctx)
    putStrLn "\n── β-rule (⊤): hcomp A ⊤ (⟨i⟩ t) u₀  ≡  t ────────────────────"
    let hTop = THComp (TVar 2)
                      (TInterval I1)
                      (PLam "i" (TVar 1))   -- t is 1 past PLam binder
                      (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["u0","t","A"] hTop
    putStrLn $ "  After:  " ++ showTerm ["u0","t","A"] (eval hTop)

    -- ── β-rule ⊥ ──────────────────────────────────────────────────────────────
    putStrLn "\n── β-rule (⊥): hcomp A ⊥ (⟨i⟩ t) u₀  ≡  u₀ ──────────────────"
    let hBot = THComp (TVar 2)
                      (TInterval I0)
                      (PLam "i" (TVar 1))
                      (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["u0","t","A"] hBot
    putStrLn $ "  After:  " ++ showTerm ["u0","t","A"] (eval hBot)

    -- ── Degenerate fill ───────────────────────────────────────────────────────
    -- ⟨i⟩ hcomp A i (⟨j⟩ x) x  :  Path A x x
    -- In context [x:A, A:U0]; at outer depth A=TVar 1, x=TVar 0
    -- Inside PLam "i": i=0, x=1, A=2
    -- Inside inner PLam "j": j=0, i=1, x=2, A=3
    putStrLn "\n── Degenerate fill: ⟨i⟩ hcomp A i (⟨j⟩ x) x  :  Path A x x ──"
    let degFill  = PLam "i"
                     (THComp (TVar 2)              -- A (past i-binder)
                             (TVar 0)              -- i
                             (PLam "j" (TVar 2))   -- ⟨j⟩ x (x past j,i binders)
                             (TVar 1))             -- x (past i-binder)
    let degFillTy = TPath (TVar 1) (TVar 0) (TVar 0)  -- Path A x x
    let ctxAx    = [("x", TVar 0), ("A", TUniv 0)]
    putStrLn $ "  Term: " ++ show degFill
    case check ctxAx degFill degFillTy of
        Right () -> putStrLn $
            "  ✓  ⟨i⟩ hcomp A i (⟨j⟩ x) x  :  Path A x x   (in context A:U0, x:A)"
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── Path transitivity ─────────────────────────────────────────────────────
    -- trans = λA x y z p q. ⟨i⟩ hcomp A i (⟨j⟩ q@j) (p@i)
    -- Depth at PLam "i" body (6 λ-binders + 1 PLam = 7):
    --   i=0, q=1, p=2, z=3, y=4, x=5, A=6
    -- Inside PLam "j" (depth 8): j=0, i=1, q=2, p=3, z=4, y=5, x=6, A=7
    putStrLn "\n── Path Transitivity (trans) via hcomp ─────────────────────────"
    let transTy =
          TPi "A" (TUniv 0) $
          TPi "x" (TVar 0) $
          TPi "y" (TVar 1) $
          TPi "z" (TVar 2) $
          TPi "p" (TPath (TVar 3) (TVar 2) (TVar 1)) $
          TPi "q" (TPath (TVar 4) (TVar 1) (TVar 0)) $
          TPath (TVar 5) (TVar 4) (TVar 3)
    let transTm =
          TAbs "A" $ TAbs "x" $ TAbs "y" $ TAbs "z" $
          TAbs "p" $ TAbs "q" $
          PLam "i"
            (THComp
               (TVar 6)                              -- A
               (TVar 0)                              -- i
               (PLam "j" (PApp (TVar 2) (TVar 0)))  -- ⟨j⟩ q@j
               (PApp (TVar 2) (TVar 0)))             -- p@i
    putStrLn $ "  trans = " ++ show transTm
    putStrLn $ "  trans : " ++ show transTy

--------------------------------------------------------------------------------
-- Glue Types Demo
--------------------------------------------------------------------------------

demoGlue :: IO ()
demoGlue = do
    putStrLn "\n=== Glue Types ==="

    -- Free variables A, T, i are represented as TVar 2, TVar 1, TVar 0
    -- in an imaginary open context [i, T, A] (index 0 = most recent)

    -- ── β-rule ⊤: Glue A ⊤ T  ≡  T ──────────────────────────────────────────
    putStrLn "\n── β-rule (⊤): Glue A ⊤ T  ≡  T ──────────────────────────────"
    let glueTop = TGlue (TVar 2) (TInterval I1) (TVar 1)
    putStrLn $ "  Before: " ++ showTerm ["i","T","A"] glueTop
    putStrLn $ "  After:  " ++ showTerm ["i","T","A"] (eval glueTop)

    -- ── β-rule ⊥: Glue A ⊥ T  ≡  A ──────────────────────────────────────────
    putStrLn "\n── β-rule (⊥): Glue A ⊥ T  ≡  A ──────────────────────────────"
    let glueBot = TGlue (TVar 2) (TInterval I0) (TVar 1)
    putStrLn $ "  Before: " ++ showTerm ["i","T","A"] glueBot
    putStrLn $ "  After:  " ++ showTerm ["i","T","A"] (eval glueBot)

    -- ── Glue type formation ───────────────────────────────────────────────────
    -- ctx: [i:𝕀, T:U0, A:U0]  → indices: i=0, T=1, A=2
    putStrLn "\n── Glue Type Formation ─────────────────────────────────────────"
    let ctxGlue = [("i", intervalTy), ("T", TUniv 0), ("A", TUniv 0)]
    let glueTy  = TGlue (TVar 2) (TVar 0) (TVar 1)
    case infer ctxGlue glueTy of
        Right ty -> putStrLn $
            "  ✓  Glue A i T  (in context A:U0, T:U0, i:𝕀)\n       : " ++ show ty
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── glue element β-rules ──────────────────────────────────────────────────
    putStrLn "\n── glue β-rule (⊤): glue ⊤ t a  ≡  t ─────────────────────────"
    let glueElemTop = TGlueElem (TInterval I1) (TVar 1) (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["a","t"] glueElemTop
    putStrLn $ "  After:  " ++ showTerm ["a","t"] (eval glueElemTop)

    putStrLn "\n── glue β-rule (⊥): glue ⊥ t a  ≡  a ─────────────────────────"
    let glueElemBot = TGlueElem (TInterval I0) (TVar 1) (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["a","t"] glueElemBot
    putStrLn $ "  After:  " ++ showTerm ["a","t"] (eval glueElemBot)

    -- ── Checking a glue element ───────────────────────────────────────────────
    -- ctx: [a:A, t:T, T:U0, A:U0, i:𝕀]  → a=0, t=1, T=2, A=3, i=4
    putStrLn "\n── glue Element Checking ───────────────────────────────────────"
    let ctxElem  = [ ("a", TVar 0)   -- a : A  (type stored as TVar 0; lookupCtx shifts it)
                   , ("t", TVar 0)   -- t : T
                   , ("T", TUniv 0)
                   , ("A", TUniv 0)
                   , ("i", intervalTy) ]
    let elemTm   = TGlueElem (TVar 4) (TVar 1) (TVar 0)     -- glue i t a
    let elemTy   = TGlue (TVar 3) (TVar 4) (TVar 2)          -- Glue A i T
    case check ctxElem elemTm elemTy of
        Right () -> putStrLn $
            "  ✓  glue i t a  :  Glue A i T   (in context A:U0, T:U0, t:T, a:A, i:𝕀)"
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── unglue β-rules ────────────────────────────────────────────────────────
    putStrLn "\n── unglue β-rule (⊤): unglue ⊤ T_e g  ≡  g ───────────────────"
    let unglueTop = TUnglue (TInterval I1) (TVar 1) (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["g","T"] unglueTop
    putStrLn $ "  After:  " ++ showTerm ["g","T"] (eval unglueTop)

    putStrLn "\n── unglue β-rule (⊥): unglue ⊥ T_e g  ≡  g ───────────────────"
    let unglueBot = TUnglue (TInterval I0) (TVar 1) (TVar 0)
    putStrLn $ "  Before: " ++ showTerm ["g","T"] unglueBot
    putStrLn $ "  After:  " ++ showTerm ["g","T"] (eval unglueBot)

    -- ── unglue type inference ─────────────────────────────────────────────────
    -- ctx: [g:Glue A i T, T:U0, A:U0, i:𝕀]  → g=0, T=1, A=2, i=3
    putStrLn "\n── unglue Type Inference ───────────────────────────────────────"
    let ctxUnglue = [ ("g", TGlue (TVar 1) (TVar 2) (TVar 0))
                    , ("T", TUniv 0), ("A", TUniv 0), ("i", intervalTy) ]
    let unglueTm  = TUnglue (TVar 3) (TVar 1) (TVar 0)
    case infer ctxUnglue unglueTm of
        Right ty -> putStrLn $
            "  ✓  unglue i T g  (in context)\n       : " ++ show ty
        Left err -> putStrLn $ "  ✗  " ++ show err

    -- ── Stuck Glue ────────────────────────────────────────────────────────────
    putStrLn "\n── Stuck Glue (neutral φ = free variable) ──────────────────────"
    let stuckGlue = TGlue (TVar 2) (TVar 0) (TVar 1)
    putStrLn $ "  Glue A i T  normalises to:  " ++ showTerm ["i","T","A"] (eval stuckGlue)

    -- ── Round-trip ────────────────────────────────────────────────────────────
    -- unglue ⊥ T (glue ⊥ t a)  ≡  a
    putStrLn "\n── Round-trip: unglue ⊥ T (glue ⊥ t a)  ≡  a ─────────────────"
    let roundTrip = TUnglue (TInterval I0) (TVar 2)
                             (TGlueElem (TInterval I0) (TVar 1) (TVar 0))
    putStrLn $ "  Before: " ++ showTerm ["a","t","T"] roundTrip
    putStrLn $ "  After:  " ++ showTerm ["a","t","T"] (eval roundTrip)