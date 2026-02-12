(** * Индукция: доказательства по индукции *)

(* ################################################################# *)
(** * Раздельная компиляция *)

(** Rocq сначала нужно будет скомпилировать [Basics.v] в [Basics.vo],
    чтобы его можно было сюда импортировать -- детальные инструкции будут
    в полной версии файла. *)

From Lectures Require Export Basics.

(* ################################################################# *)
(** * Ревью *)
(* QUIZ

    Чтобы доказать следующую теорему, какие тактики нужны кроме [intros]
    и [reflexivity]?  (A) никакие, (B) [rewrite], (C) [destruct],
    (D) и [rewrite], и [destruct], или (E) нельзя доказать теми тактиками,
    которые мы знаем.

    Theorem review1: (orb true false) = true.
*)
(* QUIZ

    Как насчёт этой?

    Theorem review2: forall b, (orb true b) = true.

    Какие тактики нужны кроме [intros] и [reflexivity]?  (A) никакие,
    (B) [rewrite], (C) [destruct], (D) и [rewrite], и [destruct], или
    (E) нельзя доказать теми тактиками, которые мы знаем.
*)
(* QUIZ

    А если поменять порядок аргументов [orb]?

    Theorem review3: forall b, (orb b true) = true.

    Какие тактики нужны кроме [intros] и [reflexivity]?  (A) никакие,
    (B) [rewrite], (C) [destruct], (D) и [rewrite], и [destruct], или
    (E) нельзя доказать теми тактиками, которые мы знаем.
*)
(* QUIZ

    А что насчёт этой?

    Theorem review4 : forall n : nat, n = 0 + n.

    (A) никакие, (B) [rewrite], (C) [destruct], (D) и [rewrite], и [destruct],
    или (E) нельзя доказать теми тактиками, которые мы знаем.
*)
(* QUIZ

    А для этой?

    Theorem review5 : forall n : nat, n = n + 0.

    (A) никакие, (B) [rewrite], (C) [destruct], (D) и [rewrite], и [destruct],
    или (E) нельзя доказать теми тактиками, которые мы знаем.
*)

(* ################################################################# *)
(** * Доказательство по индукции *)

(** Мы можем доказать, что [0] является нейтральным элементом для [+] _слева_,
    используя только [рефлексивность].  Но доказательство того, что это также
    нейтральный элемент _справа_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
(** ... застревает. *)
Proof.
  intros n.
  simpl. (* Ничего не делает! *)
Abort.

(** Разбор случаев с помощью [destruct n] тоже не позволяет особо продвинуться:
    тот случай, где мы предполагаем, что [n = 0], проходит нормально, но в
    случае, когда [n = S n'] для некоторого [n'], мы точно так же застреваем. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* пока хорошо... *)
  - (* n = S n' *)
    simpl.       (* ...а тут мы опять застряли *)
Abort.

(** Нам нужна кувалда побольше: _принцип индукции_ на натуральных числах.

    Если [P(n)] -- некоторое утверждение о натуральном числе [n], и мы хотим
    показать, что [P] выполнено для всех чисел [n], мы можем рассуждать
    следующим образом:
         - показать, что [P(O)] выполнено;
         - показать, что если выполняется [P(n')], то выполняется и [P(S n')];
         - заключить, что [P(n)] выполняется для всех [n].

    Например... *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Попробуем вместе: *)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* РАЗБИРАЕМ НА ЛЕКЦИИ *) Admitted.

(** Вот ещё один связанный факт о сложении, который нам пригодится
           в дальнейшем (доказательство оставлено в качестве упражнения). *)

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** **** Упражнение: 2 звезды, стандартное (eqb_refl)

    Следующая теорема связывает вычислительное равенство [=?] в
    [nat] с равенством по определению [=] в [bool]. *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Доказательства внутри доказательств *)

(** Новая тактика: [replace]. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  replace (n + 0 + 0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* Нам просто нужно заменить (n + m) на (m + n)... выглядит так, как будто
     add_comm должен помочь! *)
  rewrite add_comm.
  (* Не работает... Rocq переписывает не тот плюс! :-( *)
Abort.

(** Чтобы использовать [add_comm] там, где нам это нужно, мы можем заменить
    [n + m] на [m + n] с помощью [replace], а затем доказать [n + m = m + n],
    используя [add_comm]. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.

(* ################################################################# *)
(** * Больше упражнений *)

(* Эти дополнительные упражнения -- о фактах, которые будут использованы
   в следующих главах.  Однако мы не будем разбирать их доказательство
   на лекции. *)

(** **** Упражнение: 3 звезды, стандартное, очень полезное (mul_comm)

    Используя [replace], докажите [add_shuffle3].  Индукция здесь не нужна. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

(** Теперь докажите коммутативность умножения.  Возможно, Вам потребуются
    вспомогательные теоремы (которые также нужно сформулировать и доказать).
    Подсказка: чему равно [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, стандартное, по желанию (more_exercises)

    Возьмите чистый лист бумаги.  Для каждой из следующих теорем, сперва
    обдумайте, (а) можно ли доказать её только упрощениями и переписываниями,
    (б) также нужен разбор случаев ([destruct]) или (c) также требуется индукция.
    Выпишите Ваши предсказания.  Затем заполните доказательства.  (Сдавать
    листочек не нужно; это лишь предложение порефлексировать перед хакингом!) *)

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* ЗАПОЛНИТЕ ЗДЕСЬ *) Admitted.
(** [] *)

