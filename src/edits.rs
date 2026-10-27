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
    deletes.dedup_by(|rest, first| {
        first.contains_range(*rest)
    });
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

    #[test]
    fn test_deletes() {
        let src = &mut "abcdef".to_owned();
        apply_deletes([
            TextRange::at(TextSize::of("a"), TextSize::of("b")),
            TextRange::at(TextSize::of("ab"), TextSize::of("c")),
            TextRange::at(TextSize::of("abcde"), TextSize::of("f")),
        ].into(), src);
        assert_eq!(src, "ade")
    }

    #[test]
    #[should_panic = "overlap deletes 1..3 & 2..5"]
    fn test_overlaps_should_panic() {
        let src = &mut "abcdef".to_owned();
        apply_deletes([
            TextRange::at(TextSize::of("a"), TextSize::of("bc")),
            TextRange::at(TextSize::of("ab"), TextSize::of("cde")),
        ].into(), src);
    }

    #[test]
    fn test_sub_deletes() {
        let src = &mut "abcdef".to_owned();
        apply_deletes([
            TextRange::at(TextSize::of("a"), TextSize::of("bcde")),
            TextRange::at(TextSize::of("ab"), TextSize::of("c")),
            TextRange::at(TextSize::of("ab"), TextSize::of("c")),
            TextRange::at(TextSize::of("abcde"), TextSize::of("f")),
        ].into(), src);
        assert_eq!(src, "a")
    }
}
