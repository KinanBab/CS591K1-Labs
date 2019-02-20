-- Syntax
inductive term
| var  : string  → term
| abs  : string → term → term
| app  : term → term → term

-- Custom notation
instance : has_coe string term := ⟨term.var⟩
notation `λ:` x `.` t := term.abs x t
notation `[`t1 `](` t2 `)` := term.app t1 t2

-- string representation of terms
def term.repr : term -> string
| (term.var x) := x
| (term.abs x t) := "λ" ++ x ++ ".(" ++ (term.repr t) ++ ")"
| (term.app t1 t2) := "[" ++ (term.repr t1) ++ "]" ++ "(" ++ (term.repr t2) ++ ")"

instance : has_repr term := ⟨term.repr⟩

-- Example
#check [λ:"x"."x"]("y")

-- Substituation: the core of beta reduction
def substitute : term -> string -> term -> term
| t v (term.var x) :=
    if eq v x 
       then t
       else (term.var x)
| t v (term.abs x t') :=
    if eq v x
       then (term.abs x t')
       else (term.abs x (substitute t v t'))
| t v (term.app t1 t2) :=
    term.app (substitute t v t1) (substitute t v t2)

#eval (substitute "y" "x" (λ:"z"."x"))
#eval (substitute "y" "x" (λ:"x"."x"))

-- Beta reduction
inductive beta : term -> term -> Prop
| nestAbs {v: string} {t t': term} : beta t t' -> beta (term.abs v t) (term.abs v t')
| absApp {v: string} {t1 t2: term} : beta (term.app (term.abs v t1) t2) (substitute t2 v t1)
| nestApp1 {t t' t2: term} : beta t t' -> beta (term.app t t2) (term.app t' t2)
| nestApp2 {t t' t2: term} : beta t t' -> beta (term.app t2 t) (term.app t2 t')

notation t `→β`:45 t' := beta t t'

-- reflexive transative closure
inductive rStar {T} (rel: T -> T -> Prop) : T -> T -> Prop
| base : ∀ {t}, rStar t t
| trans {t1 t2 t3} : rel t1 t2 -> rStar t2 t3 -> rStar t1 t3

notation t `↠β`:45 t' := (rStar beta) t t'


-- Example
lemma silly1 : ∀ {t1 t2}, (t1 →β t2) → (t1 ↠β t2) :=
begin
  intros,
  constructor,
  apply a,
  constructor,
end

lemma silly1' (t1 t2: term) (hp: t1 →β t2) : (t1 ↠β t2) :=
begin
  apply rStar.trans,
  assumption,
  apply rStar.base,
end

-- Example 2
lemma transCut (t1 t2 t3: term) : (t1 ↠β t2) → (t2 ↠β t3) → (t1 ↠β t3) :=
begin
  intros,
  induction a,
  assumption,
  have n: (a_t2 ↠β t3), apply a_ih, from a_1,
  constructor,
  assumption,
  assumption,
end

-- normal form
def is_normal : term -> bool
| (term.var _) := tt
| (term.abs _ t') := is_normal t'
| (term.app _ _) := ff

-- left most reduction
inductive left_most_beta : term -> term -> Prop
| absApp {v: string} {t1 t2: term} :
     left_most_beta (term.app (term.abs v t1) t2) (substitute t2 v t1)
| nestApp1 {t t' t2: term} :
     left_most_beta t t' -> left_most_beta (term.app t t2) (term.app t' t2)

notation t `l→β`:45 t' := left_most_beta t t'
notation t `l↠β`:45 t' := (rStar left_most_beta) t t'


lemma single_left_subst : ∀ {t1 t2: term}, (t1 l→β t2) -> (t1 →β t2) :=
begin
 intros,
 induction a,
 constructor,
 constructor,
 assumption,
end

theorem left_most_subst : ∀ {t1 t2: term}, (t1 l↠β t2) -> (t1 ↠β t2) :=
begin
 intros,
 induction a,
 constructor,
 constructor,
 apply single_left_subst,
 exact a_a,
 assumption,
end
