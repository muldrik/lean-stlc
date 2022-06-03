import Std.Data.AssocList
open Std


-- Term type
inductive TType : Type where
  | unit : String → TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, Inhabited, DecidableEq

abbrev Context := (String → TType)

inductive Term : Type where
  | var : String → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term

#print AssocList

def Context.insert (name: String) (t : TType) (ctx : Context) := fun s => if (s = name) then t else (ctx name)

inductive CtxKeyValueExist :  (key : String) → (value : TType) → (ctx : Context) → Prop where
  | Here : CtxKeyValueExist key value (AssocList.cons key value ctxs)
  | There : (later : CtxKeyValueExist key value ctxs)
          → CtxKeyValueExist key value (AssocList.cons key' value' ctxs)

inductive CtxKeyExists : (key: String) → (ctx : Context) → Prop where
  | Here : CtxKeyExists key (AssocList.cons key value ctxs)
  | There : (later : CtxKeyExists key ctxs)
          → CtxKeyExists key (AssocList.cons key' value' ctxs)

#print Decidable

instance (name: String) (ctx: Context) : Decidable (CtxKeyExists name ctx) := by
  induction ctx
  constructor
  intro bad
  cases bad
  
  rename_i name' value' xs Ih
  cases Ih with
  | isTrue cke => cases cke
  | isFalse cke => sorry

  sorry
  exact (.isTrue (.There Ih))


inductive Maybe (p : α → Sort u) where
  | found : (a : α) → p a → Maybe p
  | unknown


inductive InContextType (name: String) (ctx: Context): Prop where
  | res : (t: TType) → (t ≠ .unit "unknown") → (ctx name = t) → InContextType name ctx


inductive OptionP (α : Prop) : Prop where
  | some (val : α) : OptionP α
  | none : OptionP α

def OptionP.bind : OptionP α → (α → OptionP β) → OptionP β
  | .some a, f => f a
  | .none, f => .none



def Context.existsPair  (ctx : Context) (name: String) (type : TType) : OptionP (CtxKeyValueExist name type ctx) := match ctx with
  | .nil => .none
  | .cons n t xs => if h : (n = name) ∧ (t = type) then .some (by (
    cases h
    rename_i eq₁ eq₂
    rewrite [eq₁, eq₂]
    exact .Here
  )) else match existsPair xs name type with
    | .some x => .some (.There x)
    | .none => .none
    
def Context.existsKey  (ctx : Context) (name: String) : OptionP (CtxKeyExists name ctx) := match ctx with
  | .nil => .none
  | .cons n t xs => if h : (n = name) then .some (by (
    rewrite [h]
    exact .Here
  )) else match existsKey xs name with
    | .some x => .some (.There x)
    | .none => .none


  
  
def Context.getValue (ctx: Context) (name: String) (keyExists: CtxKeyExists name ctx) 
: ∃ t: TType, CtxKeyValueExist name t ctx := by
  induction ctx
  cases keyExists
  rename_i name' v xs IH 
  cases keyExists with
  | Here => exists v; exact .Here
  | There laterKey => 
    have ET := IH laterKey
    cases ET
    rename_i t laterPair
    exists t
    exact .There (laterPair)
  

def Context.getValue? (ctx: Context) (name: String) : OptionP (InContextType name ctx) 
  := if h : (ctx name = .unit "undefined") then .none else by
    have kek : InContextType name ctx := .res (ctx name) h (rfl)

inductive WTTerm : (ctx : Context) → TType → Type where
  | var : ∀ t (name : String), (ctx name = t) /\ (ctx name ≠ .unit "unknown") → WTTerm ctx t
  | abs : ∀ t₂, (name : String) → (t₁ : TType) → (body : WTTerm (ctx.insert name t₁) t₂) → WTTerm ctx (.arrow t₁ t₂)
  | app : ∀ t₁ t₂, WTTerm ctx (.arrow t₁ t₂) → WTTerm ctx t₁ → WTTerm ctx t₂

  

def swapEqType (ctx : Context) (t₁ t₂ : TType) (tm : WTTerm ctx t₁) : (t₁ = t₂) → WTTerm ctx t₂ := by 
  intros A
  rewrite [← A]
  exact tm


def WTTerm_to_Term (ctx: Context) (t : TType) : (WTTerm ctx t) -> Term 
  | .var type name _ => .var name
  | .abs t₂ name t₁ body => .abs name t₁ (WTTerm_to_Term (ctx.insert name t₁) t₂ body)
  | .app t₁ t₂ l r => .app (WTTerm_to_Term ctx (.arrow t₁ t₂) l) (WTTerm_to_Term ctx t₁ r)


  -- | Term.var name , ctx=> match ctx.getValue? name with
  --   | .some ⟨e, z⟩ => (by sorry) --.found t (.var t name contextType)
  --   | .none => .unknown

def Term.typecheck : (tm : Term) → (ctx : Context) → Maybe (WTTerm ctx)
  | Term.var name , ctx=> if h : (ctx name = .unit "unknown") then .unknown
      else .found (ctx name) (.var (ctx name) name (by constructor; rfl; assumption))

  | Term.abs name t₁ tm₁, ctx₁ =>
    let ctx₂ := ctx₁.insert name t₁
    match tm₁.typecheck ctx₂ with
    | .found t₂ tm₂ => .found (.arrow t₁ t₂) (.abs t₂ name t₁ tm₂)
    | .unknown => .unknown
  | Term.app tm₁ tm₂, ctx =>
    match (tm₁.typecheck ctx, tm₂.typecheck ctx) with
    | (.found (.arrow t₁ t₂) tm₂₁, .found t₃ tm₂₂) =>
      if h : (t₃ = t₁) then .found t₂ (.app t₁ t₂ tm₂₁ (swapEqType ctx t₃ t₁ tm₂₂ h))
      else .unknown
    | _ => .unknown

def Term.inferType (tm : Term) (ctx : Context) : Option (TType) := match Term.typecheck tm ctx with
  | .found t tm => .some t
  | .unknown => .none

def emptyContext : Context := fun s => .unit "unknown"

#reduce Term.inferType ((.var "x")) (Context.insert ("x") (.arrow (.unit "a") (.unit "b")) (Context.insert "y" (.unit "a") emptyContext))
#reduce Term.inferType ((.var "y")) (Context.insert ("x") (.arrow (.unit "a") (.unit "b")) (Context.insert "y" (.unit "a") emptyContext))
#reduce Term.inferType (.app (.var "x") (.var "y")) (Context.insert ("x") (.arrow (.unit "a") (.unit "b")) (Context.insert "y" (.unit "a") emptyContext))

def correct2 (ctx: Context) (tm : Term) (t : TType) (wtt : WTTerm ctx t)
  : (tm = WTTerm_to_Term ctx t wtt) → Term.inferType tm ctx = (.some t) := by
  intros A
  induction tm generalizing t ctx
  cases wtt
  simp [WTTerm_to_Term, Term.inferType, Term.typecheck]
  rename_i type name f
  



  






  
  
  

  
  




