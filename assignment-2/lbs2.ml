type expr =
 | CstI of int
 | CstB of bool
 | Var of string
 | Let of string * expr * expr
 | Prim of string * expr * expr
 | If of expr * expr * expr
 | Fun of string * expr
 | LetRec of string * string * expr * expr
 | Call of expr * expr
 (* States, initial state, transitions and accepting states *)
 | Phi of state list * state * transition list * state list
 (* Used when entering in the scope of a policy *)
 | Frame of expr * expr
 (* Some security involved operations used in the examples and when defining sigma for DFA *)
 | Read
 | Write of string
 | Open
 | Execute of string
and state = int
and symbol = char
and transition = int * symbol * int;;

type 'v env = (string * 'v) list;;

let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x;;
 
type value =
 | Int of int
 | Closure of string * expr * value env
 | RecFunVal of string * string * expr * value env
 (* Introduced new value that represent a policy *)
 | PhiVal of dfa

and dfa =
 {
   states : state list;
   sigma : symbol list;
   start : state;
   transitions : transition list;
   accepting : state list;
 };;

(* Predefined alphabet values *)
let sigma_values = ['r'; 'w'; 'e'; 'o'];;

(* Helper functions provided for the homework *)
let states (dfa : dfa) = dfa.states;;
let addTransition t dfa = { dfa with transitions = t :: dfa.transitions };;

let explode s =
  let rec expl i l =
    if i < 0 then l else
    expl (i - 1) (s.[i] :: l) in (* s.[i] returns the ith element of s as a char *)
      expl (String.length s - 1) [];; (* String.length s returns the length of s *)

let rec contains e l =
  match l with
    | [] -> false
    | hd::tl -> if hd = e then true else contains e tl;;

let checkAccepts str dfa =
  (* Get the list of symbols. *)
  let symbols = explode str in
    (* If I'm at state {state}, where do I go on {symbol}? *)
    let transition state symbol =
      let rec find_state l =
        match l with
          | (s1,sym,s2)::tl ->
            if (s1 = state && symbol = sym) then s2 
            else find_state tl
          | _ -> failwith "no next state"
      in find_state dfa.transitions
    in let final_state =
      let rec h symbol_list =
        match symbol_list with
          | [hd] -> (transition dfa.start hd)
          | hd::tl -> (transition (h tl) hd)
          | _ -> failwith "empty list of symbols"
        in h (List.rev symbols)
      in if (contains final_state dfa.accepting) then
        true
      else
        false;;

(* 
  Helper function used to check if the active policies are satisfied at each step that involves an
  operation that is related to security
*)
let rec checkPolicies h l =
  match l with
    | [] -> true
    | hd::tl -> let res = checkAccepts h hd in
      if res then checkPolicies h tl
      else false;;

(* 
  Eval interpreter enhanced with the history of execution represented as a string and the active policies
  represented as a list of DFAs, the interpreter return a tuple that is made of a value and the updated history 
*)
let rec eval (e : expr) (env : value env) (history : string) (activePhis : dfa list) : value * string =
  match e with
    | CstI i -> (Int i, history)
    | CstB b -> (Int (if b then 1 else 0), history)
    | Var x  -> (lookup env x, history)
    | Prim(ope, e1, e2) ->
      let (v1, history') = eval e1 env history activePhis in
        let (v2, history'') = eval e2 env history' activePhis in
          begin
            match (ope, v1, v2) with
              | ("*", Int i1, Int i2) -> (Int (i1 * i2), history'')
              | ("+", Int i1, Int i2) -> (Int (i1 + i2), history'')
              | ("-", Int i1, Int i2) -> (Int (i1 - i2), history'')
              | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), history'')
              | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), history'')
              |  _ -> failwith "unknown primitive or wrong type"
          end
    | Let(x, eRhs, letBody) ->
      let (xVal, history') = eval eRhs env history activePhis in
        let letEnv = (x, xVal) :: env in
          eval letBody letEnv history' activePhis
    | If(e1, e2, e3) ->
      begin
        match eval e1 env history activePhis with
          | (Int 0, history') -> eval e3 env history' activePhis
          | (Int _, history') -> eval e2 env history' activePhis
          | _     -> failwith "eval If"
      end
    | Fun(x, fBody) -> (Closure(x, fBody, env), history)
    | LetRec(fName, par, fBody, fLet) -> 
      let env2 = (fName, (RecFunVal(fName, par, fBody, env))) :: env in
        eval fLet env2 history activePhis
    | Call(eFun, eArg) ->
      let (fClosure, history') = eval eFun env history activePhis in
        begin
          match fClosure with
            | Closure (x, fBody, fDeclEnv) ->
              let (xVal, history'') = eval eArg env history' activePhis in
                let fBodyEnv = (x, xVal) :: fDeclEnv
                  in eval fBody fBodyEnv history'' activePhis
            | _ -> failwith "eval Call: not a function"
        end
    (* Construct used to create a policy, the user cannot specify sigma because it is fixed *)
    | Phi(states, start, transitions, accepting) -> 
      let p : dfa = {
        states = states;
        sigma = sigma_values;
        start = start;
        transitions = transitions;
        accepting = accepting} 
      in (PhiVal(p), history)
    (* Block where the policy specified by phi is activated *)
    | Frame(phi, e) ->
      let (p, history') = eval phi env history activePhis in
        begin 
          match p with
            (* First check that the passed phi is a policy value *)
            | PhiVal (d) -> 
              (* If the history is empty, as in the case of an initial execution, don't check the history *)
              if (String.length history') != 0 then
                (* Check that the past history respects the policy *)
                let check = checkAccepts history' d in
                  (* Continue evaluating adding the newly appending policy into the list*)
                  if check then eval e env history' (activePhis @ [d])
                  else failwith ("eval Frame: policy not satisfied, h: " ^ history')
              else eval e env history' (activePhis @ [d])
            | _ -> failwith ("eval Frame: not a policy")
        end
    (* 
      For each of these operations, first update the history and then check if each 
      of the policies are satisfied. If all are satisfied then execute a fake op
    *)
    | Read -> 
      let history' = history ^ String.make 1 'r' in 
        let x = checkPolicies history' activePhis in
          if x then (Int 0, history')
          else failwith ("eval Read: policy not satisfied, h: " ^ history')
    | Write(x) -> 
      let history' = history ^ String.make 1 'w' in 
        let x = checkPolicies history' activePhis in
          if x then (Int 1, history')
          else failwith ("eval Write: policy not satisfied, h: " ^ history')
    | Open -> 
      let history' = history ^ String.make 1 'o' in 
        let x = checkPolicies history' activePhis in
          if x then (Int 2, history')
          else failwith ("eval Connect: policy not satisfied, h: " ^ history')
    | Execute(x) -> 
      let history' = history ^ String.make 1 'e' in 
        let x = checkPolicies history' activePhis in
          if x then (Int 3, history')
          else failwith ("eval Execute: policy not satisfied, h: " ^ history');;

(**** EXAMPLES ****)          

(* 1. Chinese wall no write after read, policy not satisfied inside frame *)
let cw = Phi([0; 1; 2], 
            0, 
            [
              (0, 'w', 0);
              (0, 'r', 1);
              (1, 'r', 1);
              (1, 'w', 2);
              (2, 'w', 2);
              (2, 'r', 2)
            ],
            [0; 1]);;
eval (Frame(cw,
            Let("x", 
                Read, 
                Let("y", 
                    Write("www"), 
                    Prim("+", CstI(1), CstI(2)))
                    ))) [] "" [];;

(* 2. Read/write only after open policy, not satisfied before entering frame *)
let rwo = Phi([0; 1; 2], 
            0, 
            [
              (0, 'o', 1);
              (0, 'r', 2);
              (0, 'w', 2);
              (1, 'r', 1);
              (1, 'w', 1);
              (1, 'o', 1);
              (2, 'o', 2);
              (2, 'r', 2);
              (2, 'w', 2);
            ],
            [0; 1]);;
eval (Let("Read/Write only after open", 
      rwo,
      Let("x", 
          Read, 
          Let("y", 
              Write("ppp"), 
              Frame(Var("Read/Write only after open"),
                    Let("o",
                        Open,
                        Let("r",
                            Read,
                            Prim("+", CstI(1), CstI(2))))))))) [] "" [];;


(* 
  2. Two nested policies: read/write after open and chinese wall, 
  the evaluation not satisfies the second frame related to chinese wall 
*)
let cw = Phi([0; 1; 2; 3], 
            0, 
            [
              (0, 'o', 1);
              (0, 'w', 3);
              (0, 'r', 3);
              (1, 'r', 2);
              (1, 'w', 1);
              (1, 'o', 1);
              (2, 'w', 3);
              (2, 'r', 2);
              (2, 'o', 2);
              (3, 'w', 3);
              (3, 'r', 3);
              (3, 'o', 3);
            ],
            [0; 1; 2]);;
let rwo = Phi([0; 1; 2], 
              0, 
              [
                (0, 'o', 1);
                (0, 'r', 2);
                (0, 'w', 2);
                (1, 'o', 1);
                (1,'r', 1);
                (1,'w', 1);
                (2, 'o', 2);
                (2, 'r', 2);
                (2, 'w', 2);
              ],
              [0; 1]);;
eval (Let("Read/Write only after open", 
      rwo,
      Let("Chinese Wall",
          cw,
          Let("o", 
              Open, 
              Let("r", 
                  Read, 
                  Frame(Var("Read/Write only after open"),
                        Let("w",
                            Write("ppp"),
                            Frame(Var("Chinese Wall"),
                                  Let("r",
                                      Read,
                                      Prim("+", CstI(1), CstI(2))))))))))) [] "" [];;
            
(* 
  3. No Execute after Open, policy satisfied
*)
let eo = Phi([0; 1; 2], 
            0, 
            [
              (0, 'o', 1);
              (0, 'e', 0);
              (0, 'w', 2);
              (0, 'r', 2);
              (1, 'r', 1);
              (1, 'w', 1);
              (1, 'o', 1);
              (1, 'e', 2);
              (2, 'r', 2);
              (2, 'w', 2);
              (2, 'e', 2);
              (2, 'o', 2);
            ],
            [0; 1]);;
eval (Let("No Execute after Open", 
      eo,
      Let("e",
          Execute("eee"),
          Let("o", 
              Open, 
              Let("r", 
                  Read, 
                  Frame(Var("No Execute after Open"),
                        Let("w",
                            Write("ppp"),
                            Let("r",
                                Read,
                                Prim("+", CstI(1), CstI(2)))))))))) [] "" [];;

(* 
  4. No Execute after Open, policy not satisfied
*)
let eo = Phi([0; 1; 2], 
            0, 
            [
              (0, 'o', 1);
              (0, 'e', 0);
              (0, 'w', 2);
              (0, 'r', 2);
              (1, 'r', 1);
              (1, 'w', 1);
              (1, 'o', 1);
              (1, 'e', 2);
              (2, 'r', 2);
              (2, 'w', 2);
              (2, 'e', 2);
              (2, 'o', 2);
            ],
            [0; 1]);;
eval (Let("No Execute after Open", 
      eo,
      Let("o", 
          Open, 
          Let("r", 
              Read, 
              Frame(Var("No Execute after Open"),
                    Let("w",
                        Write("ppp"),
                        Let("e",
                            Execute("eee"),
                            Prim("+", CstI(1), CstI(2))))))))) [] "" [];;

(* 
  5. No Execute after Open, the violation happens after the frame so the execution 
  is not stopped
*)
let eo = Phi([0; 1; 2], 
            0, 
            [
              (0, 'o', 1);
              (0, 'e', 0);
              (0, 'w', 0);
              (0, 'r', 0);
              (1, 'r', 1);
              (1, 'w', 1);
              (1, 'o', 1);
              (1, 'e', 2);
              (2, 'r', 2);
              (2, 'w', 2);
              (2, 'e', 2);
              (2, 'o', 2);
            ],
            [0; 1]);;
eval (Let("No Execute after Open", 
      eo,
      Let("r", 
          Read, 
          Let("e1", 
              Frame(Var("No Execute after Open"),
                    Let("w",
                        Write("ppp"),
                        Let("e2",
                            Execute("eee"),
                            Prim("+", CstI(1), CstI(2))))),
              Let("o",
                  Open,
                  Let("e",
                      Execute("eee"),
                      Var("e"))))))) [] "" [];;
   