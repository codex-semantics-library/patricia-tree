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

let benchmark () =
  let cfg = Benchmark.cfg ~quota:(Time.second 0.33) () in
  List.map (Benchmark.all cfg instances) Bench.tests

let analyze results =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:[| Measure.run |]
  in
  Analyze.merge ols instances
    (List.map (fun instance -> Analyze.all ols instance results) instances)

let analyze = List.map analyze

let () =
  List.iter
    (fun instance -> Bechamel_notty.Unit.add instance (Measure.unit instance))
    instances

let output_notty results =
  let open Notty_unix in
  let open Notty in
  let img window results =
    Bechamel_notty.Multiple.image_of_ols_results ~rect:window
      ~predictor:Measure.run results
  in
  let window =
    match winsize Unix.stdout with
    | Some (w, h) -> { Bechamel_notty.w; h }
    | None -> { Bechamel_notty.w = 80; h = 1 }
  in
  let img = List.map (img window) results |> I.vcat in
  output_image img;
  Format.printf "@\n"

let () = benchmark () |> analyze |> output_notty
