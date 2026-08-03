//! Serialisation must round-trip, and must not be a way round the invariants.
//!
//! The second half matters more than the first. A type whose constructor refuses
//! a latitude of 500° is no use if `serde` will hand you one anyway.

#![cfg(all(feature = "serde", feature = "std"))]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::float_cmp,
    clippy::needless_pass_by_value
)]

use bearingpro::relative_motion::{Contact, Vessel};
use bearingpro::route::{LegKind, Route};
use bearingpro::sailings::Sailing;
use bearingpro::{
    Angle, CompassCourse, Deviation, DeviationTable, Distance, Latitude, Longitude, MagneticCourse,
    Position, RelativeBearing, Speed, TrueBearing, TrueCourse, Variation,
};

fn round_trip<T>(value: T) -> T
where
    T: serde::Serialize + serde::de::DeserializeOwned,
{
    let text = serde_json::to_string(&value).expect("serialises");
    serde_json::from_str(&text).expect("deserialises")
}

#[test]
fn scalars_round_trip() {
    assert_eq!(
        round_trip(Latitude::from_degrees(50.755).unwrap()),
        Latitude::from_degrees(50.755).unwrap()
    );
    assert_eq!(
        round_trip(Longitude::from_degrees(-1.2967).unwrap()),
        Longitude::from_degrees(-1.2967).unwrap()
    );
    assert_eq!(
        round_trip(Distance::from_nautical_miles(12.5).unwrap()).nautical_miles(),
        12.5
    );
    assert_eq!(round_trip(Speed::from_knots(8.25).unwrap()).knots(), 8.25);
    assert_eq!(
        round_trip(Angle::from_degrees(-1.5).unwrap()).degrees(),
        -1.5
    );
    assert_eq!(round_trip(Variation::new(-2.7).unwrap()).degrees(), -2.7);
    assert_eq!(round_trip(Deviation::new(1.5).unwrap()).degrees(), 1.5);
    assert_eq!(
        round_trip(RelativeBearing::new(315.0).unwrap()).degrees(),
        315.0
    );
}

#[test]
fn directions_keep_their_frame_through_the_type_not_the_data() {
    let compass = CompassCourse::new(123.4).unwrap();
    assert_eq!(round_trip(compass), compass);

    // The frame is not written down: a course is just a number on the wire.
    let text = serde_json::to_string(&compass).unwrap();
    assert_eq!(text, "123.4");

    // Which means the same text reads back as any frame you ask for — the type
    // you deserialise into is what decides, exactly as it does everywhere else.
    let as_magnetic: MagneticCourse = serde_json::from_str(&text).unwrap();
    assert_eq!(as_magnetic.degrees(), 123.4);
}

#[test]
fn positions_round_trip() {
    let position = Position::from_degrees(50.755, -1.2967).unwrap();
    assert_eq!(round_trip(position), position);
}

#[test]
fn deviation_tables_round_trip() {
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, 0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4,
        -0.6, 1.2, -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, -19.2, -18.1, 1.8, -0.4,
        0.7, -0.2, 1.4, -4.4, -2.9,
    ])
    .unwrap();
    assert_eq!(round_trip(table.clone()), table);
}

#[test]
fn routes_round_trip() {
    let route = Route::new(
        vec![
            Position::from_degrees(50.1, -1.5).unwrap(),
            Position::from_degrees(49.9, -2.0).unwrap(),
            Position::from_degrees(49.7, -2.75).unwrap(),
        ],
        LegKind::GreatCircle,
    )
    .unwrap();
    let back = round_trip(route.clone());
    assert_eq!(back, route);
    assert_eq!(back.kind(), LegKind::GreatCircle);
}

#[test]
fn result_types_round_trip() {
    let sailing = Sailing {
        initial_course: TrueCourse::new(282.8).unwrap(),
        final_course: TrueCourse::new(246.1).unwrap(),
        distance: Distance::from_nautical_miles(1889.1).unwrap(),
    };
    assert_eq!(round_trip(sailing), sailing);

    let vessel = Vessel {
        course: TrueCourse::new(35.0).unwrap(),
        speed: Speed::from_knots(12.0).unwrap(),
    };
    assert_eq!(round_trip(vessel), vessel);

    let contact = Contact {
        bearing: TrueBearing::new(80.0).unwrap(),
        range: Distance::from_nautical_miles(9.0).unwrap(),
    };
    assert_eq!(round_trip(contact), contact);
}

// ---------------------------------------------------------------------------
// The part that matters: deserialisation is not a back door
// ---------------------------------------------------------------------------

#[test]
fn an_impossible_latitude_is_refused_on_the_way_in() {
    assert!(serde_json::from_str::<Latitude>("500.0").is_err());
    assert!(serde_json::from_str::<Latitude>("-91.0").is_err());
    assert!(serde_json::from_str::<Latitude>("null").is_err());
    // Longitude wraps rather than failing, as it does at construction.
    assert_eq!(
        serde_json::from_str::<Longitude>("190.0")
            .unwrap()
            .degrees(),
        -170.0
    );
}

#[test]
fn an_impossible_direction_is_refused_on_the_way_in() {
    assert!(serde_json::from_str::<TrueCourse>("400.0").is_err());
    assert!(serde_json::from_str::<TrueCourse>("-1.0").is_err());
    assert!(serde_json::from_str::<CompassCourse>("\"north\"").is_err());
    assert_eq!(
        serde_json::from_str::<TrueCourse>("360.0")
            .unwrap()
            .degrees(),
        0.0
    );
}

#[test]
fn an_impossible_correction_is_refused_on_the_way_in() {
    assert!(serde_json::from_str::<Variation>("181.0").is_err());
    assert!(serde_json::from_str::<Deviation>("-181.0").is_err());
    assert!(serde_json::from_str::<RelativeBearing>("361.0").is_err());
}

#[test]
fn a_degenerate_deviation_table_is_refused_on_the_way_in() {
    // Too few nodes.
    assert!(serde_json::from_str::<DeviationTable>("[]").is_err());
    assert!(serde_json::from_str::<DeviationTable>("[[0, 1.0]]").is_err());
    // Two entries for the same heading.
    assert!(serde_json::from_str::<DeviationTable>("[[0, 1.0], [360, 2.0]]").is_err());
    // A deviation no compass ever had.
    assert!(serde_json::from_str::<DeviationTable>("[[0, 1.0], [180, 900.0]]").is_err());

    // A sound one is accepted, and normalises its courses as usual.
    let table: DeviationTable =
        serde_json::from_str("[[-350, 1.0], [180, -2.0]]").expect("a valid table");
    assert_eq!(table.nodes().first().unwrap().course(), 10);
}

#[test]
fn a_route_that_goes_nowhere_is_refused_on_the_way_in() {
    assert!(serde_json::from_str::<Route>(r#"{"waypoints":[],"kind":"RhumbLine"}"#).is_err());
    assert!(serde_json::from_str::<Route>(
        r#"{"waypoints":[{"latitude":50.0,"longitude":-1.0}],"kind":"RhumbLine"}"#
    )
    .is_err());
    // And a waypoint that is not on the globe takes the whole route with it.
    assert!(serde_json::from_str::<Route>(
        r#"{"waypoints":[{"latitude":500.0,"longitude":-1.0},
                         {"latitude":50.0,"longitude":-1.0}],"kind":"RhumbLine"}"#
    )
    .is_err());
}

#[test]
fn non_finite_numbers_do_not_survive_the_trip() {
    // JSON has no NaN, so these arrive as text and must be rejected as text.
    for text in ["\"NaN\"", "\"inf\"", "1e400"] {
        assert!(
            serde_json::from_str::<Distance>(text).is_err(),
            "{text} should not deserialise"
        );
        assert!(serde_json::from_str::<Speed>(text).is_err(), "{text}");
        assert!(serde_json::from_str::<Angle>(text).is_err(), "{text}");
    }
}
