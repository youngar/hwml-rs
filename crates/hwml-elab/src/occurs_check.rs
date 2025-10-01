use hwml_core::{
    common::Level,
    syn::{MetavariableId, RcSyntax, Syntax},
};

enum PruningPosition {
    Flexible,
    Rigid,
}

fn merge_pruning_positions(a: PruningPosition, b: PruningPosition) -> PruningPosition {
    match (a, b) {
        (PruningPosition::Rigid, PruningPosition::Rigid) => PruningPosition::Rigid,
        _ => PruningPosition::Flexible,
    }
}

struct OccursState {
    locals: Vec<Level>,
    current: MetavariableId,
    position: PruningPosition,
}

impl OccursState {
    fn new(metavariable: MetavariableId) -> OccursState {
        OccursState {
            locals: Vec::new(),
            current: metavariable,
            position: PruningPosition::Flexible,
        }
    }

    fn local(&mut self, level: Level) {
        self.locals.push(level);
    }

    fn set_position(&mut self, position: PruningPosition) {
        self.position = position;
    }
}

fn occurs(state: &mut OccursState, term: RcSyntax) -> bool {
    // Elaborate the term to weak head normal form.

    match term.as_ref() {
        Syntax::Metavariable(meta) if meta.id == state.current => {
            state.set_position(PruningPosition::Rigid);
            return true;
        }
        _ => {
            // For now, we don't check for occurs in other syntax forms
            false
        }
    }
}

pub fn occurs_check(metavariable: MetavariableId, term: RcSyntax) -> bool {
    occurs(&mut OccursState::new(metavariable), term)
}
