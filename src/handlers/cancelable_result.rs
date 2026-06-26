use super::LngEvent;

#[derive(Clone, Debug)]
pub enum CancelableResult<R> {
    Ok(R),
    Canceled(LngEvent),
    Partial(R, LngEvent),
}

impl<R> CancelableResult<R> {
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

    pub fn map<T, F: FnOnce(R) -> T>(self, transformation: F) -> CancelableResult<T> {
        match self {
            Self::Ok(r) => CancelableResult::Ok(transformation(r)),
            Self::Canceled(lng_event) => CancelableResult::Canceled(lng_event),
            Self::Partial(r, lng_event) => CancelableResult::Partial(transformation(r), lng_event),
        }
    }

    pub fn and_then<T, F: FnOnce(R) -> CancelableResult<T>>(self, transformations: F) -> CancelableResult<T> {
        match self {
            CancelableResult::Ok(r) => transformations(r),
            CancelableResult::Canceled(lng_event) => CancelableResult::Canceled(lng_event),
            CancelableResult::Partial(r, lng_event) => match transformations(r) {
                CancelableResult::Ok(r2) => CancelableResult::Partial(r2, lng_event),
                CancelableResult::Canceled(lng_event2) => CancelableResult::Canceled(lng_event2),
                CancelableResult::Partial(r2, lng_event2) => CancelableResult::Partial(r2, lng_event2),
            },
        }
    }
}

impl<T> CancelableResult<CancelableResult<T>> {
    pub fn flatten(self) -> CancelableResult<T> {
        match self {
            CancelableResult::Ok(r) => r,
            CancelableResult::Canceled(lng_event) => CancelableResult::Canceled(lng_event),
            CancelableResult::Partial(CancelableResult::Partial(r, lng_event), _) => CancelableResult::Partial(r, lng_event),
            CancelableResult::Partial(CancelableResult::Ok(r), lng_event) => CancelableResult::Partial(r, lng_event),
            CancelableResult::Partial(CancelableResult::Canceled(lng_event), _) => CancelableResult::Canceled(lng_event),
        }
    }
}

impl<T> From<Result<T, LngEvent>> for CancelableResult<T> {
    fn from(value: Result<T, LngEvent>) -> Self {
        match value {
            Ok(r) => CancelableResult::Ok(r),
            Err(e) => CancelableResult::Canceled(e),
        }
    }
}
