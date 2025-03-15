use super::LngEvent;

#[must_use]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum LngResult<R> {
    Ok(R),
    Canceled(LngEvent),
    Partial(R, LngEvent),
}

impl<R> LngResult<R> {
    pub fn result(self) -> Option<R> {
        match self {
            Self::Canceled(_) => None,
            Self::Partial(r, _) | Self::Ok(r) => Some(r),
        }
    }

    pub const fn result_ref(&self) -> Option<&R> {
        match self {
            Self::Canceled(_) => None,
            Self::Partial(r, _) | Self::Ok(r) => Some(r),
        }
    }

    pub fn result_mut(&mut self) -> Option<&mut R> {
        match self {
            Self::Canceled(_) => None,
            Self::Partial(r, _) | Self::Ok(r) => Some(r),
        }
    }

    pub fn cancel_cause(self) -> Option<LngEvent> {
        match self {
            Self::Canceled(e) | Self::Partial(_, e) => Some(e),
            Self::Ok(_) => None,
        }
    }

    pub const fn cancel_cause_ref(&self) -> Option<&LngEvent> {
        match self {
            Self::Canceled(e) | Self::Partial(_, e) => Some(e),
            Self::Ok(_) => None,
        }
    }

    pub fn cancel_cause_mut(&mut self) -> Option<&mut LngEvent> {
        match self {
            Self::Canceled(e) | Self::Partial(_, e) => Some(e),
            Self::Ok(_) => None,
        }
    }

    pub const fn is_success(&self) -> bool {
        matches!(self, Self::Ok(_))
    }

    pub const fn is_partial(&self) -> bool {
        matches!(self, Self::Partial(_, _))
    }

    pub const fn is_canceled(&self) -> bool {
        matches!(self, Self::Canceled(_))
    }

    pub fn map<T, F: FnOnce(R) -> T>(self, transformation: F) -> LngResult<T> {
        match self {
            Self::Ok(r) => LngResult::Ok(transformation(r)),
            Self::Canceled(lng_event) => LngResult::Canceled(lng_event),
            Self::Partial(r, lng_event) => LngResult::Partial(transformation(r), lng_event),
        }
    }

    pub fn and_then<T, F: FnOnce(R) -> LngResult<T>>(self, transformations: F) -> LngResult<T> {
        match self {
            LngResult::Ok(r) => transformations(r),
            LngResult::Canceled(lng_event) => LngResult::Canceled(lng_event),
            LngResult::Partial(r, lng_event) => match transformations(r) {
                LngResult::Ok(r2) => LngResult::Partial(r2, lng_event),
                LngResult::Canceled(lng_event2) => LngResult::Canceled(lng_event2),
                LngResult::Partial(r2, lng_event2) => LngResult::Partial(r2, lng_event2),
            },
        }
    }
}

impl<T> LngResult<LngResult<T>> {
    pub fn flatten(self) -> LngResult<T> {
        match self {
            LngResult::Ok(r) => r,
            LngResult::Canceled(lng_event) => LngResult::Canceled(lng_event),
            LngResult::Partial(LngResult::Partial(r, lng_event), _) => LngResult::Partial(r, lng_event),
            LngResult::Partial(LngResult::Ok(r), lng_event) => LngResult::Partial(r, lng_event),
            LngResult::Partial(LngResult::Canceled(lng_event), _) => LngResult::Canceled(lng_event),
        }
    }
}

impl<T> From<Result<T, LngEvent>> for LngResult<T> {
    fn from(value: Result<T, LngEvent>) -> Self {
        match value {
            Ok(r) => LngResult::Ok(r),
            Err(e) => LngResult::Canceled(e),
        }
    }
}
