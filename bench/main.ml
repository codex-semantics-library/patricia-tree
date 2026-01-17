open Bechamel
open Toolkit

(** Alternative to [monotonic_clock] that works in µs/run. *)
let monotonic_clock_us =
  let module Ext = struct
    include Monotonic_clock

    let get () = get () /. 1000.
    let unit () = "µs"
  end in
  let ext = Measure.register (module Ext) in
  Measure.instance (module Ext) ext

let minor_allocated_precise =
  let module Ext = struct
    type witness = unit

    let load () = ()
    let unload () = ()
    let make () = ()
    let get () = Gc.minor_words ()
    let label () = "minor-allocated"
    let unit () = "word"
  end in
  let ext = Measure.register (module Ext) in
  Measure.instance (module Ext) ext

let instances =
  Instance.[ monotonic_clock_us; minor_allocated_precise; promoted ]

let predictors = [| Measure.run |]

let benchmark () =
  let cfg = Benchmark.cfg ~quota:(Time.second 0.33) () in
  List.map
    (fun t -> (Test.Elt.name t, Benchmark.run cfg instances t))
    (Test.expand Bench.tests)

(** Analyze the test results using OLS and return the result in a tablular
    format. *)
let analyze_to_table ~instances ~bootstrap ~r_square ~predictors :
    (string * Benchmark.t) list -> string list * (string * float list) list =
 fun results ->
  let ols = Analyze.ols ~bootstrap ~r_square ~predictors in
  let metrics =
    List.init (Array.length predictors) (fun i -> `Predictor i)
    @ if r_square then [ `R_square ] else []
  in
  let rows =
    List.map
      (fun (test_name, results) ->
        ( test_name,
          List.concat_map
            (fun inst ->
              let ols = Analyze.one ols inst results in
              let estimates =
                Option.value ~default:[] (Analyze.OLS.estimates ols)
              in
              List.map
                (function
                  | `Predictor i ->
                      Option.value ~default:Float.nan (List.nth_opt estimates i)
                  | `R_square ->
                      Option.value ~default:Float.nan (Analyze.OLS.r_square ols))
                metrics)
            instances ))
      results
  in
  let header =
    List.concat_map
      (fun inst ->
        let lbl = Measure.label inst and unit = Measure.unit inst in
        List.map
          (function
            | `Predictor i ->
                Printf.sprintf "%s (%s/%s)" lbl unit predictors.(i)
            | `R_square -> Printf.sprintf "%s (R²)" lbl)
          metrics)
      instances
  in
  (header, rows)

(** Truncated string representation with at most 3 digits after the period. *)
let nice_float_to_string f =
  let precision =
    if f < 100. then if f < 10. then 3 else 2 else if f < 1000. then 1 else 0
  in
  Printf.sprintf "%.*f" precision f

let output_csv (header, rows) =
  let rows =
    List.map
      (fun (test_name, data) -> test_name :: List.map nice_float_to_string data)
      rows
  in
  let outf = "results.csv" in
  Csv.save outf (("Test name" :: header) :: rows);
  Printf.eprintf "Output saved to %S.\n%!" outf

let () =
  benchmark ()
  |> analyze_to_table ~instances ~bootstrap:0 ~r_square:false ~predictors
  |> output_csv
