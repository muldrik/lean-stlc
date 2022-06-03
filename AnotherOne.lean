
import Std.Data.AssocList
open Std


-- Term type
inductive TType : Type where
  | unit : String → TType
--  | bool : TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, Inhabited, DecidableEq

def Context := AssocList String TType

inductive Term : Type where
--  | true : Term
--  | false : Term
  | var : String → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term
  deriving BEq, DecidableEq


inductive HasType : (ctx : Context) → Term → TType → Prop where
  | var : ∀ tm t (name : String), ctx.find? name = some t → HasType ctx (.var name) t
  | abs : ∀ (name : String) TArg TBody tmBody,
          HasType (ctx.insert name Targ) tmBody TBody
        → HasType ctx (.abs name TArg tmBody) (.arrow TArg TBody)
  | app : ∀ t₁ t₂ tm₁ tm₂,
          HasType ctx tm₁ (.arrow t₁ t₂)
        → HasType ctx tm₂ t₂
        → HasType ctx (.app tm₁ tm₂) t2




def typecheck : (ctx : Context) → (tm : Term) → Option TType
--  | Term.true, ctx => .found .bool (.true Term.true rfl)
--  | Term.false, ctx => .found .bool (.false Term.false rfl)
  | ctx, Term.var name => ctx.find? name
  | ctx, Term.abs name TArg tmBody => 
    let ctx₂ := ctx.insert name TArg 
    match typecheck ctx₂ tmBody with
      | .some TBody => .some (.arrow TArg TBody)
      | _ => .none
  | ctx, Term.app tm₁ tm₂ =>
    match (typecheck ctx tm₁, typecheck ctx tm₂) with
      | (.some (.arrow T₁₁ T₁₂), .some T₂) → 
        if (T₁₁ = T₂) then .some T₁₂ else .none 
      | (_, _) => .none
  -- | Term.abs name t₁ tm₁, ctx₁ =>
  --   let ctx₂ := ctx₁.insert name t₁
  --   match tm₁.typecheck ctx₂ with
  --   | .found t₂ tm₂ =>
  --     .found (.arrow t₁ t₂) (@WTTerm.abs ctx₁ tm₁ t₂ ctx₂ (Term.abs name t₁ tm₁) name t₁ rfl rfl tm₂)
  --   | .unknown => .unknown
  -- | Term.app tm₁ tm₂, ctx =>
  --   match (tm₁, tm₁.typecheck ctx, tm₂.typecheck ctx) with
  --   | (.abs name t' tm', .found (.arrow t₁ t₂) tm₂₁, .found t₃ tm₂₂) =>
  --     -- (swapEqType ctx t₃ t₁ tm₂₂ h)
  --     if h : (t₃ = t₁) ∧ (tm₁ = .abs name t₁ tm') then
  --       .found t₂ (.app t₁ t₂ (Term.app tm₁ tm₂) tm₁ tm₂ name tm' (by
  --         cases h <;> rename_i teq tabs
  --         rewrite [tabs]
  --         rfl
  --       ) tm₂₁ (by
  --         cases h <;> rename_i teq tabs
  --         rewrite [← teq]
  --         exact tm₂₂
  --       ) rfl)
  --     else .unknown
  --   | _ => .unknown




#print typecheck


def typecheck_correct (ctx: Context) (tm : Term) (t : TType) : (typecheck ctx tm = .some t) → HasType ctx tm t := by sorry

