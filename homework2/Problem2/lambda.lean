-- Syntax
inductive term
| var  : nat  → term
| abs  : nat → term → term
| app  : term → term → term

-- Custom notation
-- instance : has_coe nat term := ⟨term.var⟩
notation `X`n := term.var n
notation `λ:X`n `.` t := term.abs n t
notation `[`t1`]@(`t2`)` := term.app t1 t2

-- Substitution: the core of beta reduction
@[simp] def substitute : term -> nat -> term -> term
| t v (term.var x) :=
    if to_bool (x = v) then t else (term.var x)
| t v (term.abs x t') :=
    if to_bool (x = v) then (term.abs x t') else (term.abs x (substitute t v t'))
| t v (term.app t1 t2) :=
    term.app (substitute t v t1) (substitute t v t2)

-- reflexive transative closure
inductive rStar {T} (rel: T -> T -> Prop) : T -> T -> Prop
| base : ∀ {t}, rStar t t
| trans {t1 t2 t3} : rel t1 t2 -> rStar t2 t3 -> rStar t1 t3

-- beta reduction
inductive beta : term -> term -> Prop
| abs: ∀{x t t'}, beta t t' -> beta (term.abs x t) (term.abs x t')
| appl: ∀{x: nat}, ∀{t1 t1' t2: term},
       beta t1 (term.abs x t1')
       -> beta (term.app t1 t2) (term.app (term.abs x t1') t2) 
| appr: ∀{t1 t2 t2': term},
       beta t2 t2'
       -> beta (term.app t1 t2) (term.app t1 t2')
| app :∀{x: nat}, ∀{t1 t2: term},
       beta (term.app (term.abs x t1) t2) (substitute t2 x t1)

notation t `l→β`:45 t' := beta t t'
notation t `l↠β`:45 t' := (rStar beta) t t'
