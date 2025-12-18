use text_size::{TextRange, TextSize};
use smol_strc::SmolStr;
use itertools::Itertools;

pub fn apply_inserts(mut inserts: Vec<(TextSize, SmolStr)>, s: &mut String) {
    inserts.sort_by_key(|(at, _)| u32::from(*at));
    for (at, text) in inserts.iter().rev() {
        s.insert_str((*at).into(), text);
    }
}

pub fn apply_deletes(mut deletes: Vec<TextRange>, s: &mut String) {
    deletes.sort_by_key(|range| u32::from(range.start()));
    for (a, b) in deletes.iter().tuple_windows() {
        assert!(a.end() <= b.start(), "overlap deletes {a:?} & {b:?}\n{deletes:#?}");
    }
    for range in deletes.iter().rev() {
        let range = usize::from(range.start())..usize::from(range.end());
        s.drain(range);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inserts() {
        let src = &mut "adf".to_owned();
        apply_inserts([
            (TextSize::of("a"), "b".into()),
            (TextSize::of("a"), "c".into()),
            (TextSize::of("ad"), "e".into()),
        ].into(), src);
        assert_eq!(src, "abcdef")
    }
}
