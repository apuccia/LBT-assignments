module SSet = Set.Make(String);;

type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | If of expr * expr * expr
 | Fun of string * expr * SSet.t
 | Call of expr * expr;;
 
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

let rec eval (e : expr) (env : value env) (ePerm : SSet.t) =
  match e with
    | CstI i -> Int i
    | CstB b -> Int (if b then 1 else 0)
    | Var x  -> lookup env x
    | Prim(ope, e1, e2) ->
      let v1 = eval e1 env ePerm in
        let v2 = eval e2 env ePerm in
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
      let xVal = eval eRhs env ePerm in
        let letEnv = (x, xVal) :: env in
          eval letBody letEnv ePerm
    | If(e1, e2, e3) ->
      begin
        match eval e1 env ePerm with
          | Int 0 -> eval e3 env ePerm
          | Int _ -> eval e2 env ePerm
          | _     -> failwith "eval If"
      end
    | Fun(x, fBody, fReqPerm) -> 
      if SSet.subset fReqPerm permissions 
        then Closure(x, fBody, fReqPerm, env)
      else
        failwith "required permissions not supported"
    | Call(eFun, eArg) ->
      let fClosure = eval eFun env ePerm in
        begin
          match fClosure with
            | Closure (x, fBody, fPerm, fDeclEnv) ->
              if SSet.subset fPerm ePerm then
                let xVal = eval eArg env ePerm in
                  let fBodyEnv = (x, xVal) :: fDeclEnv
                    in eval fBody fBodyEnv (SSet.inter ePerm fPerm)
              else
                failwith "required permissions not satisfied"
            | _ -> failwith "eval Call: not a function"
        end;;
   
(*
  Examples
*)
  
let emptyEnv = [];;
let domPermissions = List.fold_right SSet.add ["write"] SSet.empty;;

eval (Let("inc", 
      Fun("x", Prim("+", Var("x"), CstI(1)), SSet.singleton "read"), 
      Call(Var("inc"), CstI(3)))) emptyEnv domPermissions;;