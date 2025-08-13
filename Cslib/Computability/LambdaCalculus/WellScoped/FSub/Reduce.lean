import Cslib.Computability.LambdaCalculus.WellScoped.FSub.Syntax

inductive Reduce : Exp s -> Exp s -> Prop where
| red_app_fun :
  Reduce e1 e1' ->
  Reduce (.app e1 e2) (.app e1' e2)
| red_app_arg :
  Exp.IsVal v1 ->
  Reduce e2 e2' ->
  Reduce (.app v1 e2) (.app v1 e2')
| red_app :
  Reduce (.app (.abs T e1) e2) (e1.open_var e2)
| red_tapp_fun :
  Reduce e e' ->
  Reduce (.tapp e T) (.tapp e' T)
| red_tapp :
  Reduce (.tapp (.tabs T' e) T) (e.open_tvar T)
