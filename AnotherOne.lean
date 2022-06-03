import Std.Data.AssocList
import Std.Data.HashSet
import Lean
open Std Lean Elab Meta

inductive TType : Type where
  | unit : String → TType
  | arrow : TType → TType → TType
  deriving Repr, BEq, Inhabited, DecidableEq

def Ctx := AssocList String TType

inductive Term : Type where
  | var : String → Term
  | abs : String → TType → Term → Term
  | app : Term → Term → Term
  deriving BEq, DecidableEq

declare_syntax_cat stlc_type
syntax:0 "Unit" ident : stlc_type
syntax:50 stlc_type " → " stlc_type : stlc_type
syntax:99 " ( " stlc_type " ) " : stlc_type
partial def elabSTLCType : Syntax → MetaM Expr
  | `(stlc_type| Unit $id:ident) => do
    let id := mkStrLit id.getId.toString
    mkAppM ``TType.unit #[id]
  | `(stlc_type| $l:stlc_type → $r:stlc_type) => do
    let l ← elabSTLCType l
    let r ← elabSTLCType r
    mkAppM ``TType.arrow #[l, r]
  | `(stlc_type| ($t:stlc_type) ) => elabSTLCType t
  | _ => throwUnsupportedSyntax

declare_syntax_cat stlc
syntax:0 ident : stlc
syntax:89 " λ " ident " : " stlc_type " , " stlc : stlc
syntax:1 stlc stlc : stlc
syntax:99 " ( " stlc " ) " : stlc
partial def elabSTLC : Syntax → MetaM Expr
  | `(stlc| $id:ident ) => mkAppM ``Term.var  #[mkStrLit id.getId.toString]
  | `(stlc| λ $id:ident : $t:stlc_type , $tm:stlc) => do
    let id := mkStrLit id.getId.toString
    let t ← elabSTLCType t
    let tm ← elabSTLC tm
    mkAppM ``Term.abs #[id, t, tm]
  | `(stlc| $funct:stlc $argt:stlc) => do
    let funct ← elabSTLC funct
    let argt ← elabSTLC argt
    mkAppM ``Term.app #[funct, argt]
  | `(stlc| ($tm:stlc)) => elabSTLC tm
  | `($tk) => withRef tk (throwError "Error HEre")

elab "⟪" tm:stlc "⟫" : term => elabSTLC tm

inductive HasType : (ctx : Ctx) → Term → TType → Prop where
  | var : ∀ t (name : String), ctx.find? name = some t → HasType ctx (.var name) t
  | abs : ∀ (name : String) TArg TBody tmBody,
          HasType (ctx.insert name TArg) tmBody TBody
        → HasType ctx (.abs name TArg tmBody) (.arrow TArg TBody)
  | app : ∀ t₁ t₂ tm₁ tm₂,
          HasType ctx tm₁ (.arrow t₁ t₂)
        → HasType ctx tm₂ t₁
        → HasType ctx (.app tm₁ tm₂) t₂

def typecheck : (ctx : Ctx) → (tm : Term) → Option TType
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
  : (typecheck ctx tm = .some t) → HasType ctx tm t := by
  induction tm generalizing ctx t with
  | var name =>
    simp [typecheck]; intro hfind
    exact .var t name hfind
  | abs name argₜ tm hind =>
    simp [typecheck]; split
    · rename_i P t' R
      intro hteq; injection hteq with hteq; rewrite [← hteq]; clear hteq
      exact .abs name argₜ t' tm (hind (AssocList.insert ctx name argₜ) t' R)
    · intros; contradiction
  | app tm₁ tm₂ hind₁ hind₂ =>
    simp [typecheck]; split
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
  : HasType ctx tm t → typecheck ctx tm = .some t := by
  intros hhty
  induction hhty with
  | var t name hfind =>
    simp [typecheck]; rw [hfind]
  | abs name argₜ bodyₜ body hht hbodytck =>
    simp [typecheck]; split
    · rename_i t' hargtck
      simp
      rewrite [hbodytck] at hargtck
      injection hargtck
      rename_i eq; rw [eq]
    · rename_i htof
      have hf := htof bodyₜ hbodytck
      contradiction
  | app argₜ bodyₜ funcₜₘ argₜₘ hhtbody hhtarg htck_func htck_arg =>
    simp[typecheck]; split
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

syntax "[ " ident " := " stlc "] " stlc : term

#print List

def HashSet.joinList (h₁ : HashSet String) (l : List String) : HashSet String := match l with
  | .nil => h₁
  | .cons s xs => joinList (h₁.insert s) xs


def HashSet.union (h₁ : HashSet String) (h₂ : HashSet String) : HashSet String 
  := HashSet.joinList h₁ (h₂.toList)


def Term.freeVars : (tm : Term) → (bound : HashSet String) → (acc : HashSet String) → HashSet String
  | (.var name), bound, acc => if (bound.contains name) then acc else acc.insert name
  | (.abs name _ body), bound, acc => freeVars body (bound.insert name) acc
  | (.app tm₁ tm₂), bound, acc => 
      HashSet.union (freeVars tm₁ bound acc) (freeVars tm₂ bound acc)

def freshVarHelper (freeVars: List String) (acc : String) → (acc : )

def freshVar (freeVars : HashSet String) : (∃ s, (freeVars.contains s) = false) := match (


syntax " [ " ident " := " term " ] " term : term

def Term.subst (name : String) : (src : Term) → (into : Term) → Term
  -- | src@(.var n), into => if (name = n) then into else src
  -- | src@(.abs n argT body) => if (name = n) then src else (.abs n argT )
  | src, _ => src

def 

macro_rules
  | `([ $name:ident := $into:term ] $src:term) => do
    let name := quote name.getId.toString
    `(Term.subst $name $src $into)




#reduce [a := ⟪ b ⟫] ⟪ c ⟫