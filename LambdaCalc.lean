import Std.Data.AssocList

#print Std.AssocList

inductive TType where
  | unit: String -> TType
  | arrow : TType -> TType -> TType

def Context: Type := (String → TType)

def addVarType (varName: String) (varType: TType) (ctx: Context): Context := (fun s => if (s == varName) then varType else ctx s)


inductive Expr where
  | var : String -> Expr
  | ap : Expr -> Expr -> Expr
  | lam : String → TType -> Expr -> Expr

#print Std.AssocList

inductive HasType : (context: Context) -> Expr → TType → Prop
  | var : ∀ name, HasType context (.var name) (context name)
  | ap : ∀ tm₁ tm₂ tm₃ t, HasType context tm₁ (.arrow t₁ t₂) → HasType context tm₂ t₁ -> HasType context tm₃ t2
  | lam: ∀ argName argType tm t, HasType context tm t → HasType (addVarType argName argType context) (.lam argName argType tm) (.arrow argType t)

theorem 
HasType.det (h₁ : HasType e t₁) (h₂ : 
HasType 
e 
t₂) : 
t₁ = 
t₂ := by


