open Classical


inductive Object : Type
  | mk : String → Object
  deriving Nonempty, Inhabited, DecidableEq, Repr

inductive Instant : Type
  | mk : String → Instant
  deriving Nonempty, Inhabited, DecidableEq, Repr

inductive Event : Type
  | mk : String → Event
  deriving Nonempty, Inhabited, DecidableEq, Repr


/- TIME STRUCTURE -/
opaque after (t1 t2 : Instant) : Prop

axiom after_irreflexive (t : Instant) :
    ¬ after t t

axiom after_asymmetric (t1 t2 : Instant) :
    after t1 t2 → ¬ after t2 t1

axiom after_transitive (t1 t2 t3 : Instant) :
    after t1 t2 → after t2 t3 → after t1 t3

axiom temporal_ordering :
    ∀ t1 t2, after t1 t2 ∨ t1 = t2 ∨ after t2 t1

def before (t1 t2 : Instant) : Prop :=
    after t2 t1

def directly_after (t1 t2 : Instant) : Prop :=
    after t1 t2 ∧ ¬ ∃ t3, after t1 t3 ∧ after t3 t2

theorem after_is_distinct (t1 t2 : Instant) :
    after t1 t2 → t1 ≠ t2 :=
by
    intro h1 h2
    have h3 := after_irreflexive t1
    simp_all

theorem singleton_directly_after (t1 t2 t3 : Instant) :
    directly_after t1 t2 → directly_after t1 t3 → t2 = t3 :=
by
    intro ⟨ h1, h2 ⟩ ⟨ h3, h4 ⟩
    simp_all
    have h5 := h2 t3 h3
    have h6 := h4 t2 h1
    have h7 := temporal_ordering t3 t2
    simp_all


/- EVENTS -/
opaque starts_at (e : Event) (t : Instant) : Prop
opaque ends_at (e : Event) (t : Instant) : Prop
opaque participates_in (x : Object) (e : Event) : Prop

axiom event_has_start_and_end (e : Event) :
    ∃ t1 t2, starts_at e t1 ∧ ends_at e t2

axiom event_starts_before_it_ends (e : Event) (t1 t2 : Instant) :
    starts_at e t1 ∧ ends_at e t2 → after t1 t2

axiom event_has_participants (e : Event) :
    ∃ x : Object, participates_in x e

theorem event_has_start (e : Event) :
    ∃ t, starts_at e t :=
by
    apply byContradiction
    intro h1
    have h2 := event_has_start_and_end e
    simp_all

theorem event_has_end (e : Event) :
    ∃ t, ends_at e t :=
by
    apply byContradiction
    intro h1
    have h2 := event_has_start_and_end e
    simp_all

theorem start_and_end_are_distinct (e : Event) (t1 t2 : Instant) :
    starts_at e t1 ∧ ends_at e t2 → t1 ≠ t2 :=
by
    intro ⟨ h1, h2 ⟩ h3
    have h4 := event_starts_before_it_ends e t1 t2 ⟨ h1, h2 ⟩
    have h5 := after_is_distinct t1 t2 h4
    simp_all


def InstantaneousEvent (e : Event) : Prop :=
    ∃ t1 t2: Instant, starts_at e t1 ∧ ends_at e t2 ∧ directly_after t1 t2

def SingleParticipantEvent (e : Event) : Prop :=
    ∀ x y: Object, participates_in x e → participates_in y e → x = y

/- PRESENCE -/
opaque present_at (x : Object) (t : Instant) : Prop

axiom non_returning_objects (x : Object) (t1 t2 : Instant) :
    present_at x t1 ∧ ¬ present_at x t2 → ¬ ∃ t3, after t3 t2 ∧ present_at x t3


/- COMPOSITION -/
opaque component_of (x y : Object) (t : Instant) : Prop


axiom component_irreflexive (x : Object) (t : Instant) :
    ¬ component_of x x t

axiom component_asymmetric (x y : Object) (t : Instant):
    component_of x y t → ¬ component_of y x t

axiom component_supplementation (x y : Object) (t : Instant) :
    component_of x y t → ∃ z : Object, component_of z y t ∧ x ≠ z

axiom component_presence (x y : Object) (t : Instant) :
    component_of x y t → present_at x t ∧ present_at y t

def essential_component_of (x y : Object) : Prop :=
    ∀ t : Instant, present_at y t → component_of x y t

def necessary_component_of (x y : Object) : Prop :=
    ∀ t : Instant, present_at x t ∧ component_of x y t

/- CONNECTION -/
opaque connected_to (x y : Object) (t : Instant) : Prop

axiom connected_symmetric (x y : Object) (t : Instant) :
    connected_to x y t → connected_to y x t

axiom connected_transitive (x y z : Object) (t : Instant) :
    connected_to x y t → connected_to y z t → connected_to x z t

axiom components_interconnected (x y : Object) (t : Instant) :
    ∃ z : Object, component_of x z t ∧ component_of y z t → connected_to x y t

axiom connection_presence (x y : Object) (t : Instant) :
    connected_to x y t → present_at x t ∧ present_at y t


def System (x : Object) : Prop :=
    ∃ y : Object, ∃ t : Instant, component_of y x t

def CompositionOpenSystem (x : Object) : Prop :=
    System x ∧ ∃ y t, component_of y x t ∧ ¬ essential_component_of y x

def CompositionClosedSystem (x : Object) : Prop :=
    System x ∧ ∀ y t, component_of y x t → essential_component_of y x


def SystemCreation (e : Event) : Prop :=
    SingleParticipantEvent e ∧ InstantaneousEvent e ∧
    ∃ x : Object, ∃ t1 t2 : Instant, starts_at e t1 ∧ ends_at e t2 ∧
        participates_in x e ∧ ¬ present_at x t1 ∧ present_at x t2


theorem systems_have_multiple_components :
    ∀ x, System x → ∃ y z, component_of y x ∧ component_of z x ∧ y ≠ z :=
by
    intro x h1
    have h2 := h1
    unfold System at h2
    cases h2 with
    | intro y h3 =>
        have h4 := component_supplementation y x h3
        cases h4 with
        | intro z h5 =>
            exists y
            exists z
