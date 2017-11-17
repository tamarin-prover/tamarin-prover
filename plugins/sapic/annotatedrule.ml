open Annotatedsapicaction
open Position
open Fact
open Action
open Printf
open Str

let strip_non_alphanumerical (termstring:string) = 
    let r1=regexp "[~)({}]+"
    and r2=regexp "[-$^+,<>!' ]+"
    and r3=regexp "="
    in
       global_replace r1 ""
       (global_replace r2 "_" 
        (global_replace r3 "equals" termstring))

type annotated_rule = { 
sapic_terms : annotated_sapic_action list;
position   : position;
left       : fact list;
actions    : action list;
right      : fact list;
}

let rec print_msr (msr: annotated_rule list)  = match msr with
    [] -> ""
    | head :: tail -> 
            let comment = String.concat ", " (List.map annotated_sapic_action2string head.sapic_terms) in
            let rulename =  strip_non_alphanumerical comment^"_"^(pos2string head.position) in
            let facts2string factlist= String.concat ", " (List.map fact2string factlist)
            and action_list2string al = String.concat ", " (List.map action2string al)
            in
            sprintf "rule %s: //%s \n [ %s] --[%s]-> [%s]\n\n" rulename comment (facts2string head.left) (action_list2string head.actions) (facts2string head.right) 
            ^ ( print_msr tail)

let msrs2annotated_rules sapic_terms position msrs  = 
  let disambiguate ls = List.fold_left
      (fun (rules,n) (l,a,r) ->
          (({ sapic_terms =  sapic_terms @ [Comment(string_of_int n)] ;
         position=position; 
         left=l; 
         actions=a;
         right=r;
       }::rules),n+1)) ([],0) ls
  in 
  match msrs with
    [l,a,r] -> 
        [{ sapic_terms = sapic_terms ;
          position=position; 
          left=l; 
          actions=a;
          right=r;
        }]
    | [] -> []
    | x::xs -> match disambiguate (x::xs) with (rules,_) -> List.rev rules

let msrs_subst f msr =  
    let (l,a,r) = f (msr.left,msr.actions,msr.right) in
    { 
      sapic_terms = msr.sapic_terms;
      position= msr.position;
      left  = l;
      right= r;
      actions= a;
    }
