(* file: main.ml *)
(* Assumes the parser file is "sapic.mly" and the lexer file is "lexer.mll". *)
open Printf
open Arg

open Sapic

exception ParsingError of Lexing.position * Lexing.position * string 
exception NonExistingStrategy of string 

let usage = Printf.sprintf "Usage: %s file" (Filename.basename Sys.argv.(0))
(* let usage = Printf.sprintf "Usage: %s [ -t translation ] [-l]"
 * (Filename.basename Sys.argv.(0)) *)

let translation = ref "default"
let args  = ref []

let speclist = [
    (* ("-t", Arg.String (fun name -> translation := name), ": which translation function to use"); *)
    (* ("-l", Arg.Unit (fun () -> Printf.printf "first, second\n"; exit 0), ": list available translation functions"); *)
    ("--", Arg.Rest (fun arg -> args := !args @ [arg]),
    ": stop interpreting options")
    ]


let main () =
    try
        let collect arg = args := !args @ [arg] in
        let _ = Arg.parse speclist collect usage in
        let file_name = List.hd(!args) in

        let translation_function = match !translation with
        "first" | "default" -> Firsttranslation.translation
        (*| "second"  -> Secondtranslation.translation
        | "third"  -> Thirdtranslation.translation *)
        | _ -> raise (NonExistingStrategy !translation)
        in

        let ic = open_in file_name in 
        let lexbuf = Lexing.from_channel ic in
        while true do
            try 
                let result = Sapic.input Lexer.token lexbuf in
                let output = translation_function result in
                print_endline output;
                flush stdout;
        with Parsing.Parse_error ->
            begin
                let last_pos_start = Lexing.lexeme_start_p lexbuf in
                let last_pos_end = Lexing.lexeme_end_p lexbuf in
                let tok = Lexing.lexeme lexbuf in
                raise (ParsingError(last_pos_start,last_pos_end,tok))
            end
        done
            with End_of_file -> exit 0
            | ParsingError(start_pos,end_pos,tok) -> 
                    let filename = Sys.argv.(0) in
                    let linenumber = start_pos.Lexing.pos_lnum in
                    let first_char = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol in
                    let last_char = end_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol in
                    printf "File \"%s\", line %d, characters %d-%d:\n Syntax error. Unexpected token: %S" filename linenumber first_char last_char tok
            | NonExistingStrategy(name) -> eprintf "Strategy does not exist: %s\n" name; exit (-1) 
;;

let _ = Printexc.print main ()
