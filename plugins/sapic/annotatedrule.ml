open Annotatedsapicaction
open Position
open Fact
open Action
open Printf
open Str
open Color

let strip_non_alphanumerical (termstring:string) = 
    let r1=regexp "[~)({}]+"
    and r2=regexp "[-$^+,<>!' ]+"
    and r3=regexp "="
    in
       global_replace r1 ""
       (global_replace r2 "_" 
        (global_replace r3 "equals" termstring))

type annotated_rule = { 
    process_name : string option;
    sapic_terms  : annotated_sapic_action list;
    position     : position;
    left         : fact list;
    actions      : action list;
    right        : fact list;
}

let color_table : (string, string) Hashtbl.t = Hashtbl.create 10

let rec print_msr (msr: annotated_rule list) = match msr with
    [] -> ""
    | head :: tail ->
            let comment = String.concat ", " (List.map annotated_sapic_action2string head.sapic_terms) in
            let rulename =  strip_non_alphanumerical comment^"_"^(pos2string head.position) in
            let (process_name, color) = match head.process_name with
              | Some p ->
                    let c = (try Hashtbl.find color_table p
                             with Not_found -> let n = (rgb2string (random_rgb ())) in Hashtbl.add color_table p n; n)
                    in (sprintf " [process=%s] " p, sprintf " [color=%s]" c)
              | None -> (" [process=top-level] ", "") in
            let facts2string factlist= String.concat ", " (List.map fact2string factlist)
            and action_list2string al = String.concat ", " (List.map action2string al)
            in
            sprintf "rule %s%s: //%s%s \n [%s] --[%s]-> [%s]\n\n" rulename color process_name comment (facts2string head.left) (action_list2string head.actions) (facts2string head.right) 
            ^ ( print_msr tail)

let msrs2annotated_rules sapic_terms position msrs =
  let disambiguate ls = List.fold_left
      (fun (rules,n) (l,a,r) ->
        (({
            process_name = None;
            sapic_terms  = sapic_terms @ [Comment(string_of_int n)];
            position     = position;
            left         = l;
            actions      = a;
            right        = r;
       }::rules),n+1)) ([],0) ls
  in 
  match msrs with
    | [l,a,r] ->
        [{
            process_name = None;
            sapic_terms  = sapic_terms;
            position     = position;
            left         = l;
            actions      = a;
            right        = r;
        }]
    | [] -> []
    | x::xs -> match disambiguate (x::xs) with (rules,_) -> List.rev rules

let msrs_subst f msr =  
    let (l,a,r) = f (msr.left,msr.actions,msr.right) in
    { 
      process_name = msr.process_name;
      sapic_terms = msr.sapic_terms;
      position= msr.position;
      left  = l;
      right= r;
      actions= a;
    }

let annotated_rules_update process_name ars =
    List.map (fun ar ->
        let p_n = match ar.process_name with
            Some s -> Some s
          | None -> process_name
        in
        { process_name = p_n;
          sapic_terms  = ar.sapic_terms;
          position     = ar.position;
          left         = ar.left;
          actions      = ar.actions;
          right        = ar.right; }) ars
