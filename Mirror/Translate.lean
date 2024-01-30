import Lean
import Mirror.IR
import Mirror.Extension
import Mirror.H2iiii

/-

  Todo:
  * Allow curried RandomM computations
  * Allow parametric polymorphism
  * Allow higher-order functions

  For now, because of these restrictions,
  the compilation of prob_while and prob_until is ad-hoc

-/

namespace Lean.ToDafny

def IsWFMonadic (e: Expr) : Bool :=
  match e with
  | .app (.const ``RandomM ..) _ => true
  | .forallE _ _ range _ => IsWFMonadic range
  | _ => false

partial def toDafnyTyp (e : Expr) : MetaM Typ := do
  match e with
  | .bvar .. => throwError "toDafnyTyp: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyTyp: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyTyp: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyTyp: not supported -- sort {e}"
  | .const ``Nat .. => return .nat
  | .const ``Bool .. => return .bool
  | .const ``Int .. => return .int
  | .const ``_root_.Rat .. => return .rat
  | .const .. => throwError "toDafnyTyp: not supported -- constant {e}"
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      let info ← getConstInfo name
      match name with
      | ``Prod => return .prod (← toDafnyTyp args[0]!) (← toDafnyTyp args[1]!)
      | ``RandomM => return (← toDafnyTyp args[0]!)
      | _ => throwError "Type conversion failure {fn} --- {args}"
      else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  --toDafnyTyp arg
  | .lam .. => throwError "toDafnyTyp: not supported -- lambda abstraction {e}"
  | .forallE _ domain range _ => throwError "toDafnyTyp: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyTyp: not supported -- let expressions {e}"
  | .lit .. => throwError "toDafnyTyp: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyTyp: not supported -- metadata {e}"
  | .proj .. => throwError "toDafnyTyp: not supported -- projection {e}"

def toDafnyTypTop (e: Expr) : MetaM ((List Typ) × Typ) := do
  match e with
  | .forallE _ (.sort _) _ _ => throwError "toDafnyTypTop: Polymorphism not supported yet"
  | (.app (.const ``RandomM ..) arg) => return ([],← toDafnyTyp arg)
  | .forallE _ domain range _ =>
    let r ← toDafnyTypTop range
    return ((← toDafnyTyp domain) :: r.1 , r.2)
  | _ => throwError "toDafnyTypTop: error"

def chopLambda (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => body
  | _ => e

partial def toDafnyExpr (dname : String) (env : List String) (e : Expr) : MetaM Expression := do
  match e with
  | .bvar i => return .name (env[i]!)
  | .fvar .. => throwError "toDafnyExpr: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExpr: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExpr: not supported -- sort {e}"
  | .const ``true .. => return .tr
  | .const ``false .. => return .fa
  | .const ``Coin .. => return .name "Coin"
  | .const ``PUnit.unit .. => throwError "WF: all conditions are if then else, including the ones to throw errors"
  | .const .. => throwError "toDafnyExpr: not supported -- constant {e}"
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      let info ← getConstInfo name
      match name with
      | ``pure => return .pure (← toDafnyExpr dname env args[3]!)
      | ``bind => return .bind (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``ite => return .ite (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[3]!) (← toDafnyExpr dname env args[4]!)
      | ``dite => return .ite (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname ("dummy" :: env) (chopLambda args[3]!)) (← toDafnyExpr dname ("dummy" :: env) (chopLambda args[4]!))
      | ``throwThe => return .throw (← toDafnyExpr dname env args[4]!)
      | ``prob_while => return .prob_while (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``prob_until => return .prob_until (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``OfNat.ofNat => toDafnyExpr dname env args[1]!
      | ``HAdd.hAdd => return .binop .addition (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HSub.hSub => return .binop .substraction (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HMul.hMul => return .binop .multiplication (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HDiv.hDiv => return .binop .division (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HPow.hPow => return .binop .pow (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HMod.hMod => return .binop .pow (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``Eq => return .binop .equality (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``Ne => return .binop .inequality (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``And => return .binop .conjunction (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Or => return .binop .disjunction (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Not => return .unop .negation (← toDafnyExpr dname env args[0]!)
      | ``LT.lt => return .binop .least (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``LE.le => return .binop .leastequal (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``GT.gt => return .binop .greater (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``GE.ge => return .binop .greaterequal (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``Nat.log => return .binop .log (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Nat.floor => return .unop .floor (← toDafnyExpr dname env args[3]!)
      | ``decide => toDafnyExpr dname env args[0]!
      | ``_root_.Rat.den => return .unop .denominator (← toDafnyExpr dname env args[0]!)
      | ``_root_.Rat.num => return .unop .numerator (← toDafnyExpr dname env args[0]!)
      | ``Nat.cast => toDafnyExpr dname env args[2]!
      | ``Int.cast => toDafnyExpr dname env args[2]!
      | ``Prod.fst => return .proj (← toDafnyExpr dname env args[2]!) 1
      | ``Prod.snd => return .proj (← toDafnyExpr dname env args[2]!) 2
      | ``Prod.mk => return .pair (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``Neg.neg => return .unop .minus (← toDafnyExpr dname env args[2]!)
      | ``abs => return .unop .abs (← toDafnyExpr dname env args[2]!)
      | ``OfScientific.ofScientific => toDafnyExpr dname env args[4]!
      | _ =>
        if IsWFMonadic info.type
        then
          let args' ← args.mapM (toDafnyExpr dname env)
          return .monadic name.toString args'.toList
        else throwError "toDafnyExpr: not supported -- application of {fn} to {args}"
      else if let .bvar i := fn
          -- Coin...
           then return .monadic dname [(← toDafnyExpr dname env args[0]!)]
           else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  | .lam binderName _ body _  => return (.lam binderName.toString (← toDafnyExpr dname (binderName.toString :: env) body))
  | .forallE .. => throwError "toDafnyExpr: not supported -- pi {e}"
  | .letE lhs _ rhs body _ => return (.letb lhs.toString (← toDafnyExpr dname env rhs) (← toDafnyExpr dname (lhs.toString :: env) body))
  | .lit (.natVal n) => return .num n
  | .lit (.strVal s) => return .str s
  | .mdata .. => throwError "toDafnyExpr: not supported -- meta {e}"
  | .proj .. => throwError "toDafnyExpr: not supported -- projection {e}"

partial def toDafnyExprTop (dname : String) (num_args : Nat) (names : List String) (e : Expr) : MetaM (List String × Expression) := do
  match e with
  | .bvar .. => throwError "toDafnyExprTop: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyExprTop: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExprTop: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExprTop: not supported -- sort {e}"
  | .const .. => throwError "toDafnyExprTop: not supported -- constant {e}"
  | .app .. =>
    e.withApp fun fn args =>
      if let .const ``WellFounded.fix .. := fn
      then toDafnyExprTop dname num_args names (args[4]!)
      else throwError "toDafnyExprTop: not supported -- application {e}"
  | .lam binderName _ body _ =>
    let sig_names := names ++ [binderName.toString]
    if num_args = List.length names + 1
    then
      match body with
      | (.lam _ _ body _) => return (sig_names, ← toDafnyExpr dname ("dummy" :: sig_names.reverse) (chopLambda body))
      | _ => return (sig_names, ← toDafnyExpr dname sig_names.reverse body)
    else toDafnyExprTop dname num_args sig_names body
  | .forallE .. => throwError "toDafnyExprTop: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyExprTop: not supported -- let expression {e}"
  | .lit .. => throwError "toDafnyExprTop: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyExprTop: not supported -- meta {e}"
  | .proj .. => throwError "toDafnyExprTop: not supported -- projection {e}"

def printParamTypes (params : List Typ) : String :=
  match params with
  | [] => ""
  | param :: params => s!"{param.print}, {printParamTypes params}"

def toDafnyRandomMDefIn (declName: Name) : MetaM RandomMDef := do
  let info ← getConstInfo declName
  match info with
    | ConstantInfo.defnInfo _ =>
      if IsWFMonadic info.type then
        let (inParamTyp, outParamTyp) ← toDafnyTypTop info.type
        let (inParam, body) ←  toDafnyExprTop declName.toString (List.length inParamTyp) [] info.value!
        let defn := RandomMDef.mk (declName.toString) inParamTyp outParamTyp inParam body
        return defn
      else throwError "This extractor works for RandomM monadic computations only (1)"
    | _ => throwError "This extractor works for RandomM monadic computations only (2)"

end Lean.ToDafny
