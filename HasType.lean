import Std.Data.AssocList
open Std


-- Term type
inductive TType : Type where
  | unit : String → TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, Inhabited, DecidableEq

def Context := AssocList String TType

inductive Term : Type where
  | var : String → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term

inductive HasType : (ctx : Context) → Term → TType → Prop where
  | var : ∀ t (name : String), (ctx.find? name = some t) → WTTerm ctx t
  | abs : ∀ t₂, (name : String) → (t₁ : TType) → (body : WTTerm (ctx.insert name t₁) t₂) → WTTerm ctx (.arrow t₁ t₂)
  | app : ∀ t₁ t₂, WTTerm ctx (.arrow t₁ t₂) → WTTerm ctx t₁ → WTTerm ctx t₂

inductive Maybe (p : α → Type) where
  | found : (a : α) → p a → Maybe p
  | unknown
  

#print Decidable

def swapEqType (ctx : Context) (t₁ t₂ : TType) (tm : WTTerm ctx t₁) : (t₁ = t₂) → WTTerm ctx t₂ := by 
  intros A
  rewrite [← A]
  exact tm


def WTTerm_to_Term (ctx: Context) (t : TType) : (WTTerm ctx t) -> Term 
  | .var type name _ => .var name
  | .abs t₂ name t₁ body => .abs name t₁ (WTTerm_to_Term (ctx.insert name t₁) t₂ body)
  | .app t₁ t₂ l r => .app (WTTerm_to_Term ctx (.arrow t₁ t₂) l) (WTTerm_to_Term ctx t₁ r)



def Term.typecheck : (tm : Term) → (ctx : Context) → Maybe (WTTerm ctx)
  | Term.var name , ctx=> match contextType : ctx.find? name with
    | some t => .found t (.var t name contextType)
    | none => .unknown
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

def typecheck_correct : (ctx : Context) → (t : TType) → (wtt : WTTerm ctx t) → (WTTerm_to_Term ctx t wtt).typecheck ctx = .found t wtt := by
  intros ctx t wtt
  induction (WTTerm_to_Term ctx t wtt) generalizing wtt

  