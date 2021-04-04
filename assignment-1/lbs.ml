module SSet = Set.Make(String);;

type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | If of expr * expr * expr
 (* Modified Fun construct in order to specify the set of permissions *)
 | Fun of string * expr * SSet.t
 | Call of expr * expr
 (* Added new construct to check that a given set of permissions are enabled *)
 | DemandPerm of SSet.t * expr;;

(* 
  An environment is a map from identifier to a value (what the identifier is bound to).
  For simplicity we represent the environment as an association list, i.e., a list of pair (identifier, data).
*)
type 'v env = (string * 'v) list;;

(*
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it raises an exception.
*)
let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;
 
type value =
 | Int of int
 | Closure of string * expr * SSet.t * value env;;

(* val eval : expr -> value env -> SSet.t -> value = <fun> *)
let rec eval (e : expr) (env : value env) (permDom : SSet.t) =
  match e with
    | CstI i -> Int i
    | CstB b -> Int (if b then 1 else 0)
    | Var x  -> lookup env x
    | Prim(ope, e1, e2) ->
      let v1 = eval e1 env permDom in
        let v2 = eval e2 env permDom in
          begin
            match (ope, v1, v2) with
              | ("*", Int i1, Int i2) -> Int (i1 * i2)
              | ("+", Int i1, Int i2) -> Int (i1 + i2)
              | ("-", Int i1, Int i2) -> Int (i1 - i2)
              | ("=", Int i1, Int i2) -> Int (if i1 = i2 then 1 else 0)
              | ("<", Int i1, Int i2) -> Int (if i1 < i2 then 1 else 0)
              |  _ -> failwith "unknown primitive or wrong type"
          end
    | Let(x, eRhs, letBody) ->
      let xVal = eval eRhs env permDom in
        let letEnv = (x, xVal) :: env in
          eval letBody letEnv permDom
    | If(e1, e2, e3) ->
      begin
        match eval e1 env permDom with
          | Int 0 -> eval e3 env permDom
          | Int _ -> eval e2 env permDom
          | _     -> failwith "eval If"
      end
    | Fun(x, fBody, fReqPerm) -> 
      Closure(x, fBody, fReqPerm, env)
    | Call(eFun, eArg) ->
      let fClosure = eval eFun env permDom in
        begin
          match fClosure with
            | Closure (x, fBody, fPerm, fDeclEnv) ->
              let xVal = eval eArg env permDom in
                let fBodyEnv = (x, xVal) :: fDeclEnv
                  (*  Compute intersection between function permissions and actual permissions  *)
                  in eval fBody fBodyEnv (SSet.inter permDom fPerm)
            | _ -> failwith "eval Call: not a function"
        end
    | DemandPerm(demPerm, exp) ->
      (*  
        Check that the permissions demanded can be granted (e.g if they are a subset of the actual permissions)
      *)
      if SSet.subset demPerm permDom then
        eval exp env permDom
      else
        failwith ("permissions missing: " ^ (String.concat ", " (SSet.elements (SSet.diff demPerm permDom))));;
   
(****** Examples ******)

let emptyEnv = [];;

(*
  Inherited access rights are only "read" but a function that requires "write" access is called
*)

let contextPermissions = List.fold_right SSet.add ["read"] SSet.empty;;

eval (Let("inc", 
      Fun("x", DemandPerm(SSet.singleton "write", Prim("+", Var("x"), CstI(1))), SSet.singleton "write"), 
      Call(Var("inc"), CstI(3)))) emptyEnv contextPermissions;;

(*
  Inherited access rights are empty but a function that requires "write" access is called
*)

let contextPermissions = SSet.empty;;
      
eval (Let("inc", 
      Fun("x", DemandPerm(SSet.singleton "write", Prim("+", Var("x"), CstI(1))), SSet.singleton "write"), 
      Call(Var("inc"), CstI(3)))) emptyEnv contextPermissions;;

(*
  Inherited access rights are "read" but function A that requires "read" access is called from
  function B that have no permissions.
*)

let contextPermissions = List.fold_right SSet.add ["read"] SSet.empty;;

eval (Let("A", 
          Fun("x", 
              DemandPerm(SSet.singleton "read", Prim("+", Var("x"), CstI(1))), 
              SSet.singleton "read"), 
          Let("B",
              Fun("y", 
                  Prim("*", Var("y"), Call(Var("A"), CstI(3))),
                  SSet.empty),
              Call(Var("B"), CstI(3))))) emptyEnv contextPermissions;;

(*
  Inherited access rights are "read" and "write", function A that requires "read" access is called from
  function B that have both permissions.
*)

let contextPermissions = List.fold_right SSet.add ["read"] SSet.empty;;
let bPerm = List.fold_right SSet.add ["read"; "write"] SSet.empty;;

eval (Let("A", 
          Fun("x", 
              DemandPerm(SSet.singleton "read", Prim("+", Var("x"), CstI(1))), 
              SSet.singleton "read"), 
          Let("B",
              Fun("y", 
                  Prim("*", Var("y"), Call(Var("A"), CstI(3))),
                  bPerm),
              Call(Var("B"), CstI(3))))) emptyEnv contextPermissions;;

(*
  Inherited access rights are "P1", "P2", "P3" and "P4", function calls are PD1 -> PD2 -> PD3, 
  function PD3 then checks for permission "P1" but function PD1 does not have it
*)

let contextPermissions = List.fold_right SSet.add ["P1"; "P2"; "P3"; "P4"] SSet.empty;;
let pd1Perm = List.fold_right SSet.add ["P2"; "P4"] SSet.empty;;
let pd2Perm = List.fold_right SSet.add ["P1"; "P2";] SSet.empty;;
let pd3Perm = List.fold_right SSet.add ["P1"; "P2"; "P3";] SSet.empty;;

eval (Let("PD3", 
          Fun("x", 
              DemandPerm(SSet.singleton "P1", Prim("+", Var("x"), CstI(1))),
              pd3Perm), 
          Let("PD2", 
              Fun("x", 
                  Prim("+", Var("x"), Call(Var("PD3"), CstI(3))), 
                  pd2Perm), 
              Let("PD1", 
                  Fun("x", 
                      Prim("+", Var("x"), Call(Var("PD2"), CstI(3))), 
                      pd1Perm), 
                  Call(Var("PD1"), CstI(3)))))) emptyEnv contextPermissions;;

(*
  Inherited access rights are "P1", "P2", "P3" and "P4", function calls are PD1 -> PD2 -> PD3, 
  function PD3 then checks for permission "P1" and "P3" but function PD1 does not have them both
  and function PD2 does not have "P3"
*)

let pd1Perm = List.fold_right SSet.add ["P2"; "P4"] SSet.empty;;
let pd2Perm = List.fold_right SSet.add ["P1"; "P2";] SSet.empty;;
let pd3Perm = List.fold_right SSet.add ["P1"; "P2"; "P3";] SSet.empty;;

let pd2DemPerm = List.fold_right SSet.add ["P1"; "P3"] SSet.empty;;
eval (Let("PD3", 
          Fun("x", 
              DemandPerm(pd2DemPerm, Prim("+", Var("x"), CstI(1))),
              pd3Perm), 
          Let("PD2", 
              Fun("x", 
                  Prim("+", Var("x"), Call(Var("PD3"), CstI(3))), 
                  pd2Perm), 
              Let("PD1", 
                  Fun("x", 
                      Prim("+", Var("x"), Call(Var("PD2"), CstI(3))), 
                      pd1Perm), 
                  Call(Var("PD1"), CstI(3)))))) emptyEnv contextPermissions;;


(*
  Inherited access rights are "P1", "P2", "P3" and "P4", function calls are PD1 -> PD2 -> PD3, 
  function PD3 then checks for permission "P1" and "P3" but function PD1 and PD2 does not have "P3"
*)

let pd1Perm = List.fold_right SSet.add ["P1"; "P2"; "P4"] SSet.empty;;
let pd2Perm = List.fold_right SSet.add ["P1"; "P2";] SSet.empty;;
let pd3Perm = List.fold_right SSet.add ["P1"; "P2"; "P3";] SSet.empty;;

let pd2DemPerm = List.fold_right SSet.add ["P1"; "P3"] SSet.empty;;
eval (Let("PD3", 
          Fun("x", 
              DemandPerm(pd2DemPerm, Prim("+", Var("x"), CstI(1))),
              pd3Perm), 
          Let("PD2", 
              Fun("x", 
                  Prim("+", Var("x"), Call(Var("PD3"), CstI(3))), 
                  pd2Perm), 
              Let("PD1", 
                  Fun("x", 
                      Prim("+", Var("x"), Call(Var("PD2"), CstI(3))), 
                      pd1Perm), 
                  Call(Var("PD1"), CstI(3)))))) emptyEnv contextPermissions;;