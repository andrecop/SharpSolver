
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System



// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ FUNZIONI AUSILIARIE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// --------------------------------------------------------- RAZIONALIZZA --------------------------------------------------------

let rec rationalize_aux (x : float) (q : float) =                       // funzione ausiliaria per razionalizzare,
    match x with                                                        // se non c'è resto nella divisione per 1 crea la
    | x when x % 1.0 = 0.0 -> rational (int(x), int(q))                 // frazione, altrimenti cerca il multiplo di 10
    | x when x % 1.0 <> 0.0 -> rationalize_aux (x * 10.0) (q * 10.0)    // grazie al quale il numeratore diventa intero

let rationalize (x : float) : rational = rationalize_aux x 1.0          // rationalize usa semplicemente la funzione
                                                                        // precedente ma ci risparmia degli input costanti

// ------------------------------------------------------- ESTRAPOLA GRADI -------------------------------------------------------

let monomial_degree (m : monomial) : int =                                              // estrae il grado dal monomio
    match m with
    | Monomial (coeff, deg) -> deg

let rec poly_deg_aux (l : polynomial) (q : int) : int =                                 // prende un polinomio, scorre la
    match l with                                                                        // lista di monomi che lo compongono,
    | Polynomial [] -> q                                                                // e verifica quale tra i vari monomi
    | Polynomial [Monomial (x,y)] when y >= q -> poly_deg_aux (Polynomial []) y         // ha il grado più alto, conservando
    | Polynomial [Monomial (x,y)] when y < q ->poly_deg_aux (Polynomial []) q           // tale valore, e lo usa come output
    | Polynomial (Monomial (x,y) :: ms) when y >= q -> poly_deg_aux (Polynomial ms) y
    | Polynomial (Monomial (x,y) :: ms) when y < q -> poly_deg_aux (Polynomial ms) q
    
let polynomial_degree (p : polynomial) : int = poly_deg_aux p 0                         // usa la funzione precedente,
                                                                                        // immettendo solamente il polinomio,
                                                                                        // e aggiungendo una variabile che
                                                                                        // servirà a registrare il grado del
                                                                                        // polinomio

let normalized_polynomial_degree (np : normalized_polynomial) : int =                   // conto la lunghezza dell'array che
    match np with                                                                       // comprende tutti i gradi dei vari
    | NormalizedPolynomial (np) -> Array.length np                                      // monomi e sottraggo 1 (ovvero il
                                                                                        // polinomio di grado zero) normalizza il polinomio, creando un array ordinato

// ---------------------------------------------------------- NEGAZIONI ----------------------------------------------------------
    
let monomial_negate (m : monomial) : monomial =                         // nega il monomio (ovvero il suo coefficiente)
    match m with                                                        // e mantiene il grado costante
    | Monomial (coeff, deg) -> Monomial (-coeff, deg)

let polynomial_negate (p : polynomial) : polynomial =                   // prende un polinomio, ne scorre la lista di
    match p with                                                        // monomi, e li nega con la funzione realizzata
    | Polynomial (l) -> Polynomial (List.map monomial_negate l)         // in precedenza per negare i singoli monomi

// --------------------------------------------------- NORMALIZZA IL POLINOMIO ---------------------------------------------------

let rec normalize_aux (p : polynomial) (q : int) (r : polynomial) (a: rational[]) (t : rational) : normalized_polynomial =
    match p with
    | Polynomial [] when q < 0 -> NormalizedPolynomial (a)                                          // normalizza il polinomio
    | Polynomial [] when q >= 0 -> normalize_aux r (q - 1) r (Array.append [|t|] a) (rational.Zero) // creando un array ordinato
    | Polynomial (x) ->                                                                             // per grado, nel quale,
        match x with                                                                                // in ciascuna posizione è
        | [Monomial (coeff, deg)] ->                                                                // presente il coefficiente
            if q = deg then normalize_aux (Polynomial []) q r a (t + coeff)                         // del grado corrispondente
            else normalize_aux (Polynomial []) q r a t                                              // a tale posizione, ad
        | Monomial (coeff, deg) :: ms ->                                                            // esempio, prendendo "2x"
            if q = deg then normalize_aux (Polynomial ms) q r a (t + coeff)                         // verrà creato un array
            else normalize_aux (Polynomial ms) q r a t                                              // del tipo "[| 0 ; 2 |]"

    // Forma alternativa (senza "if-then-else") che matcha il polinomio:

        // | Polynomial [Monomial (x, y)] when q = y -> normalize_aux (Polynomial []) q r a (t + x)
        // | Polynomial [Monomial (x, y)] when q <> y -> normalize_aux (Polynomial []) q r a t
        // | Polynomial (Monomial (x, y) :: ms) when q = y -> normalize_aux (Polynomial ms) q r a (t + x)
        // | Polynomial (Monomial (x, y) :: ms) when q <> y -> normalize_aux (Polynomial ms) q r a t
    
let normalize (p : polynomial) : normalized_polynomial = normalize_aux p (polynomial_degree p) p [||] (rational.Zero)

    // "normalize" usa la funzione precedente, prendendo un polinomio, ed estrapolandone il grado così da passare entrambi
    // così da passare entrambi alla funzione precedente e permetterle di creare un array ordinato e suddiviso per gradi



// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ FUNZIONI SECONDARIE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// ------------------------------------------------------ DERIVATE SEMPLICI ------------------------------------------------------
   
let derive_monomial (m : monomial) : monomial =                                                 // preso un monomio, ne effettua
    match m with                                                                                // una semplice derivazione,
    | Monomial (coeff, deg) when deg = 0 -> Monomial (rational.Zero, 0)                         // moltiplicando il grado per il
    | Monomial (coeff, deg) when deg > 0 -> Monomial ((rational (deg, 1) * coeff), (deg - 1))   // coefficiente, e riducendone
                                                                                                // il grado di uno

let rec derive_aux (p : polynomial) (q : 'a list) : polynomial =                                // deriva un polinomio,
    match p with                                                                                // scomponendolo in monomi
    | Polynomial [] -> Polynomial (q)                                                           // e passandoli alla funzione
    | Polynomial [x] -> derive_aux (Polynomial []) (q @ [derive_monomial x])                    // precedente che li deriva
    | Polynomial (x :: xs) -> derive_aux (Polynomial (xs)) (q @ [derive_monomial x])            // singolarmente

let derive (p : polynomial) : polynomial = derive_aux p []                                      // sfrutta la funzione precedente
                                                                                                // passando il polinomio
                                                                                                // assegnato e una lista vuota
                                                                                                // che andrà a contenere i monomi
                                                                                                // e che sarà poi riconcertita
                                                                                                // in un polinomio

// ---------------------------------------------------------- ESTRATTORE ---------------------------------------------------------

let rec extract_poly_from_expr (e : expr) : polynomial =                        // presa una espressione, ne estrae il polinomio
    match e with                                                                // al suo interno nel caso di una derivata o di
    | Poly (x) -> x                                                             // derivate multiple, continua a cercare
    | Derive (x) -> extract_poly_from_expr x                                    // ricorsivamente il polinomio al suo interno

let extract_monomial_list_from_polynomial (p : polynomial) : monomial list =    // preso un polinomio, ne estrae la lista di
    match p with                                                                // monomi al suo interno
    | Polynomial (x) -> x

// -------------------------------------------------------- SEMPLIFICATORE -------------------------------------------------------

let rec reduce_aux (q : polynomial) (p : polynomial) (m : monomial) (v : int) (r : monomial list) (t : rational) : polynomial =
    match q with
    | Polynomial [] when v <= 0 ->                                                                      // prende un polinomio
        Polynomial (r)                                                                                  // e lo riduce,
    | Polynomial [] when v > 0 ->                                                                       // scomponendolo in
        reduce_aux p p (Monomial (rational.Zero, 0)) (v - 1) (r @ [Monomial (t, v)]) (rational.Zero)    // monomi, e sommando
    | Polynomial [Monomial (coeff, deg)] when deg = v ->                                                // tra loro i monomi
        reduce_aux (Polynomial []) p m v r (t + coeff)                                                  // di grado simile,
    | Polynomial [Monomial (coeff, deg)] when deg <> v ->                                               // infine riconverte
        reduce_aux (Polynomial []) p m v r t                                                            // la lista appena
    | Polynomial (Monomial (coeff, deg) :: ms) when deg = v ->                                          // creata in un polinomio
        reduce_aux (Polynomial (ms)) p m v r (t + coeff)
    | Polynomial (Monomial (coeff, deg) :: ms) when deg <> v ->
        reduce_aux (Polynomial (ms)) p m v r t

let reduce (e : expr) : polynomial =                                                                    // sfrutta la funzione
    reduce_aux (extract_poly_from_expr e) (extract_poly_from_expr e) (Monomial (rational.Zero, 0))      // precedente, passandole
        (polynomial_degree (extract_poly_from_expr e)) [] (rational.Zero)                               // tutti i termini
                                                                                                        // necessari
// ------------------------------------------------------- DERIVATE MULTIPLE -----------------------------------------------------

let rec multi_derive (e : expr) (q : int) (p : polynomial) : polynomial =       // prende un'espressione che necessita di più
    match e with                                                                // derivazioni e la riduce, contando nel
    | Derive (g) -> multi_derive g (q + 1) (reduce g)                           // frattempo quante volte deve derivarla
    | Poly (f) ->                                                               // ed effettua ricorsivamente la derivazione
        match q with                                                            // sul polinomio finale, dando in uscita il
        | q when q>0 -> multi_derive e (q-1) (derive p)                         // polinomio derivato, tante volte quante
        | q when q=0 -> p                                                       // indicate
        


// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ FUNZIONI PRINCIPALI ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

// ---------------------------------------------------- EQUAZIONI DI GRADO ZERO --------------------------------------------------

let solve0 (np : normalized_polynomial) : bool =                            // dopo aver semplificato o derivato il polinomio di
    match np with                                                           // una equazione, nel caso risulti un polinomio di
    | NormalizedPolynomial (np) when np.[0] = rational(0,1) -> true         // grado zero, lo pone uguale a zero e ne verifica
    | NormalizedPolynomial (np) when np.[0] <> rational(0,1) -> false       // l'uguaglianza

// ---------------------------------------------------- EQUAZIONI DI PRIMO GRADO -------------------------------------------------

let solve1 (np : normalized_polynomial) : rational =                        // dopo aver semplificato o derivato il polinomio di
    match np with                                                           // una equazione, nel caso risulti un polinomio di
    | NormalizedPolynomial (np) -> (((~-)(np.[0]))/(np.[1]))                // grado uno, ne trova la soluzione, ovvero la "x" per
                                                                            // la quale l'uguaglianza è verificata

// --------------------------------------------------- EQUAZIONI DI SECONDO GRADO ------------------------------------------------

let delta (np : normalized_polynomial) : rational =                                                 // trova il discriminante
    match np with                                                                                   // dell'equazione, ovvero:
    | NormalizedPolynomial (np) ->                                                                  //   -->   b^2-4ac   <--
        ((np.[1])**2)+(~-)((rational(4,1)*(np.[2])*(np.[0])))                                       // dove "a" e "b" sono
                                                                                                    // rispettivamente i
                                                                                                    // coefficienti del secondo
                                                                                                    // e del primo grado, mentre
                                                                                                    // "c" è il coefficiente del
                                                                                                    // grado zero

let sol_2a (np : rational[]) : rational = rational(2,1)*(np.[2])                                    // trova "2a", che servirà in
                                                                                                    // seguito per facilitare i
                                                                                                    // calcoli di "x1,2"

let sol_x0 (np : normalized_polynomial) : float =                                                   // trova la soluzione nel caso
    match np with                                                                                   // in cui il delta sia pari
    | NormalizedPolynomial (np) -> float (((~-)(np.[1]))/(sol_2a np))                               // a zero (unica soluzione)

let sol_x1 (np : normalized_polynomial) : float =                                                   // trova la prima soluzione
    match np with                                                                                   // nel caso di delta positivo
    | NormalizedPolynomial (np) ->                                                                  // (ovvero quella positiva):
        (((float((~-)(np.[1]))+(sqrt(delta (NormalizedPolynomial np)))))/(float (sol_2a (np))))     // -> (-b+sqrt(delta))/2a <-

let sol_x2 (np : normalized_polynomial) : float =                                                   // trova la seconda soluzione
    match np with                                                                                   // nel caso di delta positivo
    | NormalizedPolynomial (np) ->                                                                  // (ovvero quella negativa):
        (((float((~-)(np.[1]))-(sqrt(delta (NormalizedPolynomial np)))))/(float (sol_2a (np))))     // -> (-b-sqrt(delta))/2a <-

let solve2 (np : normalized_polynomial) : (float * float option) option =                           // verifica il polinomio e
    match np with                                                                                   // dopo aver verificato il
    | NormalizedPolynomial (np) ->                                                                  // delta, restituisce una,
        if ((delta (NormalizedPolynomial (np))) = (rational.Zero))                                  // due, o nessuna soluzione
            then Some ((sol_x0 (NormalizedPolynomial (np))), None)
        elif ((delta (NormalizedPolynomial (np))) >= (rational.One))
            then Some ((sol_x1 (NormalizedPolynomial (np))), Some (sol_x2 (NormalizedPolynomial (np))))
                else None


// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ FINE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~