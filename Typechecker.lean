import Std.Data.AssocList
import Lean
open Std Lean Elab Meta

inductive TType : Type where
  | unit : String → TType
  | arrow : TType → TType → TType
  deriving BEq, Inhabited, DecidableEq

inductive Term : Type where
  | var : String → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term
  deriving BEq, DecidableEq

def Ctx := AssocList String TType

inductive HasType : (ctx : Ctx) → Term → TType → Prop where
  | var : ∀ t (name : String), ctx.find? name = some t → HasType ctx (.var name) t
  | abs : ∀ (name : String) TArg TBody tmBody,
          HasType (ctx.insert name TArg) tmBody TBody
        → HasType ctx (.abs name TArg tmBody) (.arrow TArg TBody)
  | app : ∀ t₁ t₂ tm₁ tm₂,
          HasType ctx tm₁ (.arrow t₁ t₂)
        → HasType ctx tm₂ t₁
        → HasType ctx (.app tm₁ tm₂) t₂


def Term.typecheck : (ctx : Ctx) → (tm : Term) → Option TType
  | ctx, Term.var name => ctx.find? name
  | ctx, Term.abs name TArg tmBody =>
    let ctx₂ := ctx.insert name TArg
    match typecheck ctx₂ tmBody with
      | .some TBody => .some (.arrow TArg TBody)
      | _ => .none
  | ctx, Term.app tm₁ tm₂ =>
      match (typecheck ctx tm₁, typecheck ctx tm₂) with
        | (.some (.arrow T₁₁ T₁₂), .some T₂) =>
          if (T₁₁ = T₂) then .some T₁₂ else .none
        | (_, _) => .none


theorem Prod.eq_split : (a, b) = (c, d) → a = c ∧ b = d := by
  intro h; cases h
  constructor <;> rfl

theorem If.ttype_decided {a b t t' : TType}
  : (Q : ((if a = b then Option.some t else Option.none) = Option.some t'))
  → a = b /\ t = t' := by
  split <;> intros
  · constructor
    · assumption
    · rename_i l r; injection r; assumption
  · contradiction

theorem typecheck_sound (ctx: Ctx) (tm : Term) (t : TType)
  : (Term.typecheck ctx tm = .some t) → HasType ctx tm t := by
  induction tm generalizing ctx t with
  | var name =>
    simp [Term.typecheck]; intro hfind
    exact .var t name hfind
  | abs name argₜ tm hind =>
    simp [Term.typecheck]; split
    · rename_i P t' R
      intro hteq; injection hteq with hteq; rewrite [← hteq]; clear hteq
      exact .abs name argₜ t' tm (hind (AssocList.insert ctx name argₜ) t' R)
    · intros; contradiction
  | app tm₁ tm₂ hind₁ hind₂ =>
    simp [Term.typecheck]; split
    · rename_i t₁₁ t₁₂ t₂ hp
      intro hq; cases Prod.eq_split hp
      · rename_i hterm₁type hterm₂type
        let abstype := TType.arrow t₁₁ t₁₂
        have ht₁ := hind₁ ctx abstype hterm₁type
        have ht₂ := hind₂ ctx t₂ hterm₂type
        cases If.ttype_decided hq
        · rename_i hteq₁ hteq₂
          rw [← hteq₂]; rw [← hteq₁] at ht₂
          exact .app t₁₁ t₁₂ tm₁ tm₂ ht₁ ht₂
    · intro; contradiction

theorem typecheck_complete (ctx : Ctx) (tm : Term) (t : TType)
  : HasType ctx tm t → Term.typecheck ctx tm = .some t := by
  intros hhty
  induction hhty with
  | var t name hfind =>
    simp [Term.typecheck]; rw [hfind]
  | abs name argₜ bodyₜ body hht hbodytck =>
    simp [Term.typecheck]; split
    · rename_i t' hargtck
      simp
      rewrite [hbodytck] at hargtck
      injection hargtck
      rename_i eq; rw [eq]
    · rename_i htof
      have hf := htof bodyₜ hbodytck
      contradiction
  | app argₜ bodyₜ funcₜₘ argₜₘ hhtbody hhtarg htck_func htck_arg =>
    simp[Term.typecheck]; split
    · rename_i t₁₁ t₁₂ t₂ hp
      simp_all
      cases hp
      · rename_i hargbodyt _ -- hargt
        cases hargbodyt
        simp [*] at *
        rename_i hteq
        rw [hteq]
        simp
    · simp_all
      rename_i prod fst snd hprod happ
      simp_all
      cases happ
      · rename_i hfstt hsndt
        have fstEq := Eq.symm hfstt
        have sndEq := Eq.symm hsndt
        exact (hprod argₜ bodyₜ argₜ fstEq sndEq)

#reduce Term.typecheck ((AssocList.empty.insert "x" (.arrow (.unit "a") (.unit "b"))).insert "y" (.unit "a")) (.app (.var "x") (.var "y"))

-- Syntax trees

declare_syntax_cat stlc_type
syntax:0 ident : stlc_type
syntax:50 stlc_type " → " stlc_type : stlc_type
syntax:99 " ( " stlc_type " ) " : stlc_type


macro_rules
  | `(stlc_type| $id:ident) =>
    let id := quote id.getId.toString
    `(TType.unit $id)
  | `(stlc_type| $l:stlc_type → $r:stlc_type) => `(TType.arrow $l $r)
  | `(stlc_type| ($t:stlc_type)) => `($t)

declare_syntax_cat stlc
syntax:0 ident : stlc
syntax:89 " λ " ident " : " stlc_type " , " stlc : stlc
syntax:1 stlc stlc : stlc
syntax:99 " ( " stlc " ) " : stlc
syntax " ⟪ " stlc " ⟫ " : term

macro_rules
  | `(stlc| $id:ident ) =>
    let id := quote id.getId.toString
    `(Term.var $id)
  | `(stlc| λ $id:ident : $t:stlc_type , $tm:stlc) =>
    let id := quote id.getId.toString
    `(Term.abs $id $t $tm)
  | `(stlc| $funct:stlc $argt:stlc) =>
    `(Term.app $funct $argt)
  | `(stlc| ($tm:stlc)) => `($tm)
  | `(⟪ $tm:stlc ⟫) => `($tm)

syntax " ⦃ " (ident " : " stlc_type),* " ⦄ " : term
macro_rules
  | `(⦃ $[$key:ident : $value:stlc_type],* ⦄) =>
    let key := key.map (quote ·.getId.toString)
    `([$[($key, $value)],*].toAssocList)

-- Pretty printers

def TType.str (pr : Nat) : (t : TType) → String
  | .unit s => s
  | .arrow a b => if (pr > 3)
    then ("(" ++ (a.str pr)  ++ " → " ++ (b.str pr) ++ ")")
    else (a.str 4)  ++ " → " ++ (b.str 3)

instance : Repr TType where
  reprPrec a _ := TType.str 3 a

def Term.str (pr : Nat) : (tm : Term) → String
  | .var name => name
  | .abs name argT body =>
    let s := "λ " ++ name ++ " : " ++ (argT.str 3) ++ ", " ++ (body.str 3)
    if pr > 3 then "(" ++ s ++ ")" else s  
  | .app tm₁@(.abs _ _ _) tm₂ => (tm₁.str 4) ++ " " ++ tm₂.str 3 
  | .app tm₁ tm₂ => (tm₁.str 3) ++ " " ++ (tm₂.str 3)

instance : Repr Term where
  reprPrec a _ := Term.str 3 a


def String.wrap (s left right : String) := left ++ s ++ right

def Ctx.str (pr : Nat) (ctx : Ctx) : String := (match ctx with
  | .nil => ""
  | .cons name type (.nil) => name ++ " : " ++ type.str pr
  | .cons name type xs => name ++ " : " ++ type.str pr ++ ", "
).wrap "{" "}"

instance : Repr Ctx where
  reprPrec ctx pr := ctx.str pr

instance : Repr (Option TType) where
  reprPrec opt pr := match opt with
    | .some type => reprPrec type 3
    | .none => "No type"

-- Examples


#eval ⟪ λ x : a, x ⟫
#eval Term.typecheck ⦃⦄ ⟪ λ x : a, λ y : b, λ z : d, x ⟫
#eval Term.typecheck ⦃x : a → b → c⦄ ⟪ x ⟫
#eval Term.typecheck ⦃ x : α → β, y : α ⦄ ⟪ x y ⟫
#eval Term.typecheck ⦃⦄ ⟪ (λ x : a, λ y : a → b, y x) ⟫

#eval Term.typecheck ⦃z : γ⦄ ⟪ (λ x : (α → β) → γ, x) (λ y : α → β, z) ⟫