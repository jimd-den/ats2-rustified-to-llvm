(* 4-Dimensional Todo List in ATS2 *)

// Dimension 1 (Time): Start timestamp `s` and Due timestamp `d`
// Dimension 2 (Priority): Priority level `p` (1 = high, 5 = low)
// Dimension 3 (Effort): Estimated hours `e`
// Dimension 4 (Depth): Dependency depth `depth`

datatype Task4D =
  | Task of (int, int, int, int, string)

datatype TodoList4D =
  | Nil4D
  | Cons4D of (Task4D, TodoList4D)

// 1. Total count of tasks
fun count_tasks (xs: TodoList4D): int =
  case xs of
  | Nil4D() => 0
  | Cons4D(_, rest) => 1 + count_tasks(rest)

// 2. Sum of total effort hours across all tasks (Dimension 3)
fun total_effort (xs: TodoList4D): int =
  case xs of
  | Nil4D() => 0
  | Cons4D(Task(_, _, _, effort, _), rest) => effort + total_effort(rest)

// 3. Count high-priority tasks (Dimension 2: priority = 1)
fun count_high_priority (xs: TodoList4D): int =
  case xs of
  | Nil4D() => 0
  | Cons4D(Task(_, _, p, _, _), rest) =>
      if p = 1 then 1 + count_high_priority(rest)
      else count_high_priority(rest)

// 4. Validate time coordinates (Dimension 1: s <= d)
fun valid_time (s: int, d: int): bool =
  s <= d

implement main0 () =
  let
    // Task(start, due, priority, effort_hours, title)
    val t1 = Task(0, 10, 1, 4, "Write parser")
    val t2 = Task(10, 20, 2, 8, "Implement LLVM IR emitter")
    val t3 = Task(20, 30, 1, 2, "Build interactive REPL")

    val queue = Cons4D(t1, Cons4D(t2, Cons4D(t3, Nil4D())))
  in
    println!("=== 4D Todo List ===");
    println!("Total tasks: ", count_tasks(queue));
    println!("Total effort: ", total_effort(queue), " hours");
    println!("Urgent tasks (P1): ", count_high_priority(queue));
    println!("T1 time constraint valid: ", valid_time(0, 10))
  end
