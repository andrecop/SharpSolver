(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open System
open Prelude
open Microsoft.FSharp.Text
open Impl


// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

let norm fmt = chout ConsoleColor.Yellow "norm" fmt
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt   

// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input

        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing

            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)

            | Cmd "studente" ->
                out "%s" (string ("\nProgramma implementato da\n     Andrea Coppetta\n      A.A. 2018/19\n    Matricola: 873849"))

            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni

            | Expr e1 ->                                                                    // prende un espressione
                match e1 with
                | Poly e1 ->                                                                // -> nel caso sia un polinomio
                    let np = string (normalize e1)                                          // lo normalizza
                    let deg1 = string ((normalized_polynomial_degree (normalize e1)) - 1)   // ne estrae il grado
                    hout "redux" "%O" line
                    hout "norm" "%s" np                                                     // restituisce il risulato della normalizzazione
                    hout "degree" "%s" deg1                                                 // restituisce il grado

                | Derive e1 ->                                                              // -> nel caso sia una derivata
                    let de = (derive (reduce e1))                                           //
                    let dp = string (de)
                    let np = string (normalize de)
                    let deg1 = string ((normalized_polynomial_degree (normalize de)) - 1)
                    hout "redux" "%s" dp
                    hout "norm" "%s" np
                    hout "degree" "%s" deg1

            | Equ (e1, e2) ->                                                               // prende una equazione del tipo:
                match e1, e2 with                                                           //      -->  "e1 = e2"  <--
                | Poly e1, Poly e2 ->                                                       // -> nel caso siano due polinomi
                    let n2 = polynomial_negate e2                                           // nega il secondo polinomio
                    let p1 = extract_monomial_list_from_polynomial e1                       // estrae la lista di monomi dal primo polinomio
                    let p2 = extract_monomial_list_from_polynomial n2                       // estrae la lista di monomi dal secondo polinomio
                    let np = normalize (Polynomial (p1@p2))                                 // unisce le due liste di monomi e le riconverte in un polinomio, infine lo normalizza
                    let snp = string np                                                     // converte il polinomio appena normalizzato in stringa
                    let deg = (normalized_polynomial_degree (normalize e1)) - 1             // estrae il grado del polinomio
                    let sdeg = string deg                                                   // converte il grado in stringa
                    hout "redux" "%O" line
                    hout "norm" "%s = 0" snp                                                // restituisce il risulato della normalizzazione
                    hout "degree" "%s" sdeg                                                 // restituisce il grado
                    if deg = 0                                                              // nel caso sia una equazione di grado zero
                        then hout "ident" "%s" (string (solve0 np))                         // utilizza solve0 (vedi Impl.fs)
                    elif deg = 1                                                            // nel caso sia una equazione di primo grado
                        then hout "sol" "x = %s" (string (solve1 np))                       // utilizza solve1 (vedi Impl.fs)
                    elif deg = 2                                                            // nel caso sia una equazione di secondo grado
                        then match (solve2 np) with                                         // utilizza solve2 (vedi Impl.fs)
                             | Some(x, None) -> hout "sol" "x = %s" (string x)              // e restituisce una soluzione nel caso di delta uguale a zero
                             | Some (x, Some (y)) ->                                        // o due nel caso di delta positivo
                                hout "sol" "x1 = %s  vel  x2 = %s" (string x) (string y)
                          
                | Poly e1, Derive e2 ->                                                     // -> nel caso siano uno un polinomio e l'altra un derivata
                    let de = (multi_derive e2 1 (Polynomial []))                            // deriva la seconda espressione (dopo averla ridotta)
                    let dp2 = string (de)                                                   // converte la precedente funzione in stringa
                    let np1 = string (normalize e1)                                         // normalizza il primo polinomio
                    let n2 = polynomial_negate de                                           // nega il polinomio a destra dell'uguaglianza
                    let p1 = extract_monomial_list_from_polynomial e1                       // estrae la lista di monomi dal polinomio
                    let p2 = extract_monomial_list_from_polynomial n2                       // estrae la lista di monomi dalla derivata
                    let np = normalize (Polynomial (p1@p2))                                 // unisce le due liste di monomi e converte la lista derivante in un polinomio
                    let snp = string np                                                     // converte la precedente funzione in stringa
                    let deg = (normalized_polynomial_degree (np)) - 1                       // estrae il grado dal polinomio appena generato
                    let sdeg = string deg                                                   // converte la precedente funzione in stringa
                    hout "redux" "%s = %s" np1 dp2                                          // riduce i due polinomi (dopo la derivazione) senza normalizzarli
                    hout "norm" "%s = 0" snp                                                // restituisce il risulato della normalizzazione
                    hout "degree" "%s" sdeg                                                 // restituisce il grado
                    if deg = 0                                                              // nel caso sia una equazione di grado zero
                        then hout "ident" "%s" (string (solve0 np))                         // utilizza solve0 (vedi Impl.fs)
                    elif deg = 1                                                            // nel caso sia una equazione di primo grado
                        then hout "sol" "x = %s" (string (solve1 np))                       // utilizza solve1 (vedi Impl.fs)
                    elif deg = 2                                                            // nel caso sia una equazione di secondo grado
                        then match (solve2 np) with                                         // utilizza solve2 (vedi Impl.fs)
                             | Some(x, None) -> hout "sol" "x = %s" (string x)              // e restituisce una soluzione nel caso di delta uguale a zero
                             | Some (x, Some (y)) ->                                        // o due nel caso di delta positivo
                                hout "sol" "x1 = %s  vel  x2 = %s" (string x) (string y)

                | Derive e1, Poly e2 ->                                                     // -> nel caso siano uno un polinomio e l'altra un derivata
                    let de = (multi_derive e1 1 (Polynomial []))                            // deriva la prima espressione (dopo averla ridotta)
                    let dp1 = string (de)                                                   // converte la precedente funzione in stringa
                    let np2 = string (normalize e2)                                         // normalizza il secondo polinomio
                    let n2 = polynomial_negate e2                                           // nega il polinomio a destra dell'uguaglianza
                    let p1 = extract_monomial_list_from_polynomial de                       // estrae la lista di monomi dalla derivata
                    let p2 = extract_monomial_list_from_polynomial n2                       // estrae la lista di monomi dal polinomio
                    let np = normalize (Polynomial (p1@p2))                                 // unisce le due liste di monomi e converte la lista derivante in un polinomio
                    let snp = string np                                                     // converte la precedente funzione in stringa
                    let deg = (normalized_polynomial_degree (np)) - 1                       // estrae il grado dal polinomio appena generato
                    let sdeg = string deg                                                   // converte la precedente funzione in stringa
                    hout "redux" "%s = %s" dp1 np2                                          // riduce i due polinomi (dopo la derivazione) senza normalizzarli
                    hout "norm" "%s = 0" snp                                                // restituisce il risulato della normalizzazione
                    hout "degree" "%s" sdeg                                                 // restituisce il grado
                    if deg = 0                                                              // nel caso sia una equazione di grado zero
                        then hout "ident" "%s" (string (solve0 np))                         // utilizza solve0 (vedi Impl.fs)
                    elif deg = 1                                                            // nel caso sia una equazione di primo grado
                        then hout "sol" "x = %s" (string (solve1 np))                       // utilizza solve1 (vedi Impl.fs)
                    elif deg = 2                                                            // nel caso sia una equazione di secondo grado
                        then match (solve2 np) with                                         // utilizza solve2 (vedi Impl.fs)
                             | Some(x, None) -> hout "sol" "x = %s" (string x)              // e restituisce una soluzione nel caso di delta uguale a zero
                             | Some (x, Some (y)) ->                                        // o due nel caso di delta positivo
                                hout "sol" "x1 = %s  vel  x2 = %s" (string x) (string y)

                | Derive e1, Derive e2 ->                                                   // -> nel caso siano due derivate
                    let de1 = (multi_derive e1 1 (Polynomial []))                           // deriva la prima espressione (dopo averla ridotta)
                    let de2 = (multi_derive e2 1 (Polynomial []))                           // deriva la seconda espressione (dopo averla ridotta)
                    let dp1 = string (de1)                                                  // converte la prima funzione in stringa
                    let dp2 = string (de2)                                                  // converte la seconda funzione in stringa
                    let n2 = polynomial_negate de2                                          // nega il polinomio a destra dell'uguaglianza
                    let p1 = extract_monomial_list_from_polynomial de1                      // estrae la lista di monomi dalla derivata di sinistra
                    let p2 = extract_monomial_list_from_polynomial n2                       // estrae la lista di monomi dalla derivata di destra (negata)
                    let np = normalize (Polynomial (p1@p2))                                 // unisce le due liste di monomi e converte la lista derivante in un polinomio
                    let snp = string np                                                     // converte la precedente funzione in stringa
                    let deg = (normalized_polynomial_degree (np)) - 1                       // estrae il grado dal polinomio appena generato
                    let sdeg = string deg                                                   // converte la precedente funzione in stringa
                    hout "redux" "%s = %s" dp1 dp2                                          // riduce i due polinomi (dopo la derivazione) senza normalizzarli
                    hout "norm" "%s = 0" snp                                                // restituisce il risulato della normalizzazione
                    hout "degree" "%s" sdeg                                                 // restituisce il grado
                    if deg = 0                                                              // nel caso sia una equazione di grado zero
                        then hout "ident" "%s" (string (solve0 np))                         // utilizza solve0 (vedi Impl.fs)
                    elif deg = 1                                                            // nel caso sia una equazione di primo grado
                        then hout "sol" "x = %s" (string (solve1 np))                       // utilizza solve1 (vedi Impl.fs)
                    elif deg = 2                                                            // nel caso sia una equazione di secondo grado
                        then match (solve2 np) with                                         // utilizza solve2 (vedi Impl.fs)
                             | Some(x, None) -> hout "sol" "x = %s" (string x)              // e restituisce una soluzione nel caso di delta uguale a zero
                             | Some (x, Some (y)) ->                                        // o due nel caso di delta positivo
                                hout "sol" "x1 = %s  vel  x2 = %s" (string x) (string y)    

            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code


