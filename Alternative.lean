import Std.Data.AssocList
open Std

-- Term type
inductive TType : Type where
  | bool : TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Term : Type where
  | true : Term
  | false : Term
  | var : String → Term
  /- `tif` because Lean4 can't parse just `if` -/
  | tif : Term → Term → Term → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term

inductive WTTerm : TType → Type where
  | true : WTTerm .bool
  | false : WTTerm .bool
  | var : ∀ t, String → WTTerm t
  | tif : ∀ t, (cond : WTTerm .bool) → (tb : WTTerm t) → (fb : WTTerm t) → WTTerm t
  | abs : ∀ t₂, (name : String) → (t₁ : TType) → (body : WTTerm t₂) → WTTerm (.arrow t₁ t₂)
  | app : ∀ t₁ t₂, WTTerm (.arrow t₁ t₂) → WTTerm t₁ → WTTerm t₂

inductive Maybe (p : α → Type) where
  | found : (a : α) → p a → Maybe p
  | unknown
  

#print Decidable

def swapEqType (t₁ t₂ : TType) (tm : WTTerm t₁) : (t₁ = t₂) → WTTerm t₂ := by 
  intros A
  rewrite [← A]
  exact tm


def WTTerm_to_Term (t : TType) : (WTTerm t) -> Term 
  | .true => .true
  | .false => .false
  | .var type name => .var name
  | .tif t cond tb fb => .tif (WTTerm_to_Term .bool cond) (WTTerm_to_Term t tb) (WTTerm_to_Term t fb)
  | .abs t₂ name t₁ body => .abs name t₁ (WTTerm_to_Term t₂ body)
  | .app t₁ t₂ l r => .app (WTTerm_to_Term (.arrow t₁ t₂) l) (WTTerm_to_Term t₁ r)



def Term.typecheck : (tm : Term) → (ctx : AssocList String TType) → Maybe (WTTerm)
  | Term.true, ctx => .found .bool .true
  | Term.false, ctx => .found .bool .false
  | Term.var name , ctx=> match ctx.find? name with
    | some t => .found t (.var t name)
    | none => .unknown
  | Term.tif tm₁ tm₂ tm₃, ctx =>
    match (tm₁.typecheck ctx, tm₂.typecheck ctx, tm₃.typecheck ctx) with
    | (.found (.bool) tm₁, .found t₂ tm₂, .found t₃ tm₃) =>
      if h : (t₃ = t₂) then  .found t₂ (.tif t₂ tm₁ tm₂ (swapEqType t₃ t₂ tm₃ h))
      else .unknown
    | _ => .unknown
  | Term.abs name t₁ tm₁, ctx₁ =>
    let ctx₂ := ctx₁.insert name t₁
    match tm₁.typecheck ctx₂ with
    | .found t₂ tm₂ => .found (.arrow t₁ t₂) (.abs t₂ name t₁ tm₂)
    | .unknown => .unknown
  | Term.app tm₁ tm₂, ctx =>
    match (tm₁.typecheck ctx, tm₂.typecheck ctx) with
    | (.found (.arrow t₁ t₂) tm₂₁, .found t₃ tm₂₂) =>
      if h : (t₃ = t₁) then .found t₂ (.app t₁ t₂ tm₂₁ (swapEqType t₃ t₁ tm₂₂ h))
      else .unknown
    | _ => .unknown

def Term.deriveType : (tm : Term) → (ctx : AssocList String TType) → Maybe (TType) := match (Term.typecheck tm ctx) with
  | .found .bool .true => .found .bool


theorem typecheck_correct (t derived: TType) (wtt : WTTerm t) (ctx: AssocList String TType) : (Term.typecheck (TTerm_to_Term t wtt) ctx = .found (wtt₂ derived)) → t = derived := by

