//! Reading angles and positions the way they are written down.
//!
//! One parser serves latitude, longitude and plain angles, because they are
//! written the same way: whole degrees, then optional minutes, then optional
//! seconds, with an optional hemisphere letter at either end.
//!
//! What is deliberately *not* accepted is the run-together form NMEA uses,
//! `5045.300` for 50°45.3′. It cannot be told apart from the decimal degrees
//! `5045.300`, and guessing at a position is not a service worth providing.

use alloc::string::String;

use crate::error::{NavigationError, Result};

/// Longest input the parser will look at.
///
/// Any real position is far shorter; the limit is there so that a pathological
/// input cannot turn into pathological work.
const MAX_INPUT: usize = 64;

/// The pieces of a parsed sexagesimal value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Sexagesimal {
    /// The value in degrees, always positive.
    pub(crate) magnitude: f64,
    /// The hemisphere letter, upper case, if one was given.
    pub(crate) hemisphere: Option<char>,
    /// Whether an explicit minus sign was given.
    pub(crate) negative: bool,
}

impl Sexagesimal {
    /// The signed value, taking the hemisphere letter or the sign into account.
    ///
    /// `negative_letters` says which letters mean a negative value: `"S"` for a
    /// latitude, `"W"` for a longitude.
    pub(crate) fn signed(self, negative_letters: &str) -> f64 {
        let negative = self.negative
            || self
                .hemisphere
                .is_some_and(|letter| negative_letters.contains(letter));
        if negative {
            -self.magnitude
        } else {
            self.magnitude
        }
    }
}

/// Parses `50°45.3'`, `50 45 18`, `-50.755`, `N50 45.3` and the like.
///
/// # Errors
///
/// Returns [`NavigationError::Parse`] for anything it cannot make sense of.
pub(crate) fn sexagesimal(what: &'static str, input: &str) -> Result<Sexagesimal> {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.len() > MAX_INPUT {
        return Err(parse_error(what, input));
    }

    let mut hemisphere = None;
    let mut body = trimmed;

    // A hemisphere letter may lead or trail, but there can be only one.
    if let Some(letter) = leading_hemisphere(body) {
        hemisphere = Some(letter);
        body = body.get(1..).unwrap_or_default().trim_start();
    }
    if let Some(letter) = trailing_hemisphere(body) {
        if hemisphere.is_some() {
            return Err(parse_error(what, input));
        }
        hemisphere = Some(letter);
        body = body
            .get(..body.len().saturating_sub(1))
            .unwrap_or_default()
            .trim_end();
    }
    if body.chars().any(is_hemisphere_letter) {
        return Err(parse_error(what, input));
    }

    let mut negative = false;
    if let Some(rest) = body.strip_prefix('-') {
        negative = true;
        body = rest.trim_start();
    } else if let Some(rest) = body.strip_prefix('+') {
        body = rest.trim_start();
    }
    // A sign and a hemisphere together say the same thing twice, and might
    // disagree.
    if negative && hemisphere.is_some() {
        return Err(parse_error(what, input));
    }

    let groups = numeric_groups(body).ok_or_else(|| parse_error(what, input))?;
    let magnitude = combine(&groups).ok_or_else(|| parse_error(what, input))?;

    Ok(Sexagesimal {
        magnitude,
        hemisphere,
        negative,
    })
}

/// Splits a position into its latitude and longitude halves.
///
/// # Errors
///
/// Returns [`NavigationError::Parse`] if the two halves cannot be told apart.
pub(crate) fn split_position(input: &str) -> Result<(&str, &str)> {
    let trimmed = input.trim();
    if trimmed.is_empty() || trimmed.len() > MAX_INPUT * 2 {
        return Err(parse_error("position", input));
    }

    let north_south = trimmed
        .char_indices()
        .find(|(_, c)| matches!(c, 'N' | 'n' | 'S' | 's'));
    let east_west = trimmed
        .char_indices()
        .find(|(_, c)| matches!(c, 'E' | 'e' | 'W' | 'w'));

    match (north_south, east_west) {
        (Some((latitude_index, letter)), Some((longitude_index, _))) => {
            if longitude_index <= latitude_index {
                // Longitude first, or the letters interleaved: not a form we read.
                return Err(parse_error("position", input));
            }
            let split = if latitude_index == 0 {
                // A leading hemisphere: `N50 45.3 W001 17.8`.
                longitude_index
            } else {
                // A trailing one: `50 45.3 N 001 17.8 W`.
                latitude_index + letter.len_utf8()
            };
            let latitude = trimmed
                .get(..split)
                .ok_or_else(|| parse_error("position", input))?;
            let longitude = trimmed
                .get(split..)
                .ok_or_else(|| parse_error("position", input))?;
            Ok((latitude.trim(), longitude.trim()))
        }
        (None, None) => {
            // Plain decimal degrees, separated by a comma or by space.
            let mut parts = trimmed.split([',', ';']).map(str::trim);
            let (Some(latitude), Some(longitude), None) =
                (parts.next(), parts.next(), parts.next())
            else {
                let mut words = trimmed.split_whitespace();
                let (Some(latitude), Some(longitude), None) =
                    (words.next(), words.next(), words.next())
                else {
                    return Err(parse_error("position", input));
                };
                return Ok((latitude, longitude));
            };
            Ok((latitude, longitude))
        }
        _ => Err(parse_error("position", input)),
    }
}

/// Builds the error, keeping a bounded copy of what was offered.
pub(crate) fn parse_error(what: &'static str, input: &str) -> NavigationError {
    NavigationError::Parse {
        what,
        input: input.chars().take(MAX_INPUT).collect(),
    }
}

fn is_hemisphere_letter(character: char) -> bool {
    matches!(character, 'N' | 'n' | 'S' | 's' | 'E' | 'e' | 'W' | 'w')
}

fn leading_hemisphere(body: &str) -> Option<char> {
    let first = body.chars().next()?;
    is_hemisphere_letter(first).then(|| first.to_ascii_uppercase())
}

fn trailing_hemisphere(body: &str) -> Option<char> {
    let last = body.chars().next_back()?;
    is_hemisphere_letter(last).then(|| last.to_ascii_uppercase())
}

/// Splits the body into its one, two or three numeric groups.
fn numeric_groups(body: &str) -> Option<[Option<f64>; 3]> {
    let mut groups: [Option<f64>; 3] = [None; 3];
    let mut found = 0_usize;
    let mut current = String::new();

    let flush = |current: &mut String, groups: &mut [Option<f64>; 3], found: &mut usize| {
        if current.is_empty() {
            return true;
        }
        let Ok(value) = current.parse::<f64>() else {
            return false;
        };
        current.clear();
        let Some(slot) = groups.get_mut(*found) else {
            return false;
        };
        *slot = Some(value);
        *found += 1;
        true
    };

    for character in body.chars() {
        if character.is_ascii_digit() || character == '.' {
            current.push(character);
        } else if matches!(character, '°' | '\'' | '"' | '′' | '″' | ' ' | ':' | '\t') {
            if !flush(&mut current, &mut groups, &mut found) {
                return None;
            }
        } else {
            // Anything else — a stray letter, a second sign — is not a number.
            return None;
        }
    }
    if !flush(&mut current, &mut groups, &mut found) {
        return None;
    }

    (found > 0).then_some(groups)
}

/// Turns degrees, minutes and seconds into a single value in degrees.
fn combine(groups: &[Option<f64>; 3]) -> Option<f64> {
    let degrees = groups.first().copied().flatten()?;
    let minutes = groups.get(1).copied().flatten();
    let seconds = groups.get(2).copied().flatten();

    if !degrees.is_finite() {
        return None;
    }
    // Only the last group given may have a fractional part: `50°45.3'` is a
    // position, `50.5°45.3'` is a mistake.
    if minutes.is_some() && !crate::math::is_integral(degrees) {
        return None;
    }

    let mut total = degrees;
    if let Some(minutes) = minutes {
        if !(0.0..60.0).contains(&minutes) {
            return None;
        }
        if seconds.is_some() && !crate::math::is_integral(minutes) {
            return None;
        }
        total += minutes / 60.0;
    }
    if let Some(seconds) = seconds {
        if !(0.0..60.0).contains(&seconds) {
            return None;
        }
        total += seconds / 3600.0;
    }

    total.is_finite().then_some(total)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn decimal_degrees() {
        let parsed = sexagesimal("latitude", "50.755").unwrap();
        assert_eq!(parsed.magnitude, 50.755);
        assert_eq!(parsed.hemisphere, None);
        assert!(!parsed.negative);
        assert_eq!(parsed.signed("S"), 50.755);
    }

    #[test]
    fn degrees_and_minutes() {
        for input in ["50°45.3'", "50 45.3", "50:45.3", "50°45.3′"] {
            let parsed = sexagesimal("latitude", input).unwrap();
            assert!((parsed.magnitude - 50.755).abs() < 1e-12, "{input}");
        }
    }

    #[test]
    fn degrees_minutes_and_seconds() {
        for input in ["50°45'18\"", "50 45 18", "50:45:18"] {
            let parsed = sexagesimal("latitude", input).unwrap();
            assert!((parsed.magnitude - 50.755).abs() < 1e-12, "{input}");
        }
    }

    #[test]
    fn hemispheres_lead_or_trail() {
        for input in ["50°45.3'N", "N50°45.3'", "n 50 45.3", "50 45.3 n"] {
            let parsed = sexagesimal("latitude", input).unwrap();
            assert_eq!(parsed.hemisphere, Some('N'), "{input}");
            assert!((parsed.signed("S") - 50.755).abs() < 1e-12);
        }
        let south = sexagesimal("latitude", "50°45.3'S").unwrap();
        assert!((south.signed("S") + 50.755).abs() < 1e-12);
    }

    #[test]
    fn signs_work_where_hemispheres_are_absent() {
        let negative = sexagesimal("longitude", "-1 17.8").unwrap();
        assert!(negative.negative);
        assert!((negative.signed("W") + 1.296_666_667).abs() < 1e-9);
        assert!(sexagesimal("longitude", "+1 17.8").unwrap().magnitude > 0.0);
    }

    #[test]
    fn nonsense_is_refused() {
        for input in [
            "",
            "   ",
            "north",
            "50 45.3 NW",
            "-50 45.3 N",  // a sign and a hemisphere disagreeing
            "50 60.0",     // sixty minutes is the next degree
            "50 45 60",    // and sixty seconds the next minute
            "50 45 18 12", // one group too many
            "50.5 45.3",   // fractional degrees with minutes as well
            "50 45.5 18",  // fractional minutes with seconds as well
            "50°45.3'W'N",
            "fifty",
            "50,45",
            "1e400",
        ] {
            assert!(
                sexagesimal("latitude", input).is_err(),
                "{input} should not parse"
            );
        }
        // Absurdly long input is refused rather than chewed over.
        let long = "1".repeat(200);
        assert!(sexagesimal("latitude", &long).is_err());
    }

    #[test]
    fn positions_split_at_the_hemisphere_letters() {
        for input in [
            "50°45.3'N 001°17.8'W",
            "50 45.3 N 001 17.8 W",
            "N50°45.3' W001°17.8'",
            "  50°45.3'N   001°17.8'W  ",
        ] {
            let (latitude, longitude) = split_position(input).unwrap();
            assert!(
                sexagesimal("latitude", latitude).is_ok(),
                "{input} -> {latitude:?}"
            );
            assert!(
                sexagesimal("longitude", longitude).is_ok(),
                "{input} -> {longitude:?}"
            );
        }
    }

    #[test]
    fn positions_split_on_a_separator_when_there_are_no_letters() {
        for input in ["50.755, -1.2967", "50.755 -1.2967", "50.755;-1.2967"] {
            let (latitude, longitude) = split_position(input).unwrap();
            assert!((sexagesimal("latitude", latitude).unwrap().magnitude - 50.755).abs() < 1e-9);
            assert!(sexagesimal("longitude", longitude).unwrap().negative);
        }
    }

    #[test]
    fn unsplittable_positions_are_refused() {
        for input in [
            "",
            "50.755",
            "50.755 -1.2967 extra",
            "W001°17.8' 50°45.3'N", // longitude first
            "50°45.3'N",
        ] {
            assert!(split_position(input).is_err(), "{input} should not split");
        }
    }
}
