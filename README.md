# bearingpro

[![crates.io](https://img.shields.io/crates/v/bearingpro.svg)](https://crates.io/crates/bearingpro)
[![docs.rs](https://docs.rs/bearingpro/badge.svg)](https://docs.rs/bearingpro)
[![CI](https://github.com/xvi-xv-xii-ix-xxii-ix-xiv/bearingpro/actions/workflows/ci.yml/badge.svg)](https://github.com/xvi-xv-xii-ix-xxii-ix-xiv/bearingpro/actions/workflows/ci.yml)

Marine navigation in Rust: compass corrections, the sailings, dead reckoning,
position fixing and collision avoidance.

| Module | What it does |
|---|---|
| [`angle`] | courses and bearings that carry their reference frame in the type |
| [`units`] | angles, distances and speeds, so knots cannot be mistaken for metres per second |
| [`position`] | latitude, longitude, and the chart conventions for writing them |
| [`deviation`] | deviation tables from a swing, periodic interpolation, A–E coefficients |
| [`navigation_solutions`] | compass ⇄ magnetic ⇄ true, gyro error, the current triangle |
| [`sailings`] | rhumb line, great circle, WGS-84 geodesic, cross-track error |
| [`dead_reckoning`] | DR and estimated positions, traverses, leeway, passage times |
| [`fix`] | position lines, bearing and range fixes, cocked hats, distance off |
| [`relative_motion`] | CPA and TCPA, radar plotting, the avoiding manoeuvre |
| [`route`] | passage plans: legs, distances, schedule, progress along the track |

[`angle`]: https://docs.rs/bearingpro/latest/bearingpro/angle/index.html
[`units`]: https://docs.rs/bearingpro/latest/bearingpro/units/index.html
[`position`]: https://docs.rs/bearingpro/latest/bearingpro/position/index.html
[`deviation`]: https://docs.rs/bearingpro/latest/bearingpro/deviation/index.html
[`navigation_solutions`]: https://docs.rs/bearingpro/latest/bearingpro/navigation_solutions/index.html
[`sailings`]: https://docs.rs/bearingpro/latest/bearingpro/sailings/index.html
[`dead_reckoning`]: https://docs.rs/bearingpro/latest/bearingpro/dead_reckoning/index.html
[`fix`]: https://docs.rs/bearingpro/latest/bearingpro/fix/index.html
[`relative_motion`]: https://docs.rs/bearingpro/latest/bearingpro/relative_motion/index.html
[`route`]: https://docs.rs/bearingpro/latest/bearingpro/route/index.html

**No panics** on caller-supplied data, **no `unsafe`**, and **no dependencies**
in the default configuration. Optional `no_std`.

Every example below is compiled and run as part of the test suite.

## Install

```toml
[dependencies]
bearingpro = "0.12"
```

For a bare-metal target:

```toml
[dependencies]
bearingpro = { version = "0.12", default-features = false, features = ["libm"] }
```

With `serde`, for storing and sending the value types:

```toml
[dependencies]
bearingpro = { version = "0.12", features = ["serde"] }
```

Minimum supported Rust version: 1.81.

> **Upgrading?** 0.12 is additive: routes, string parsing, shape-preserving
> interpolation and `serde`. 0.11 added positions, the sailings, dead reckoning,
> fixes and relative motion, and moved speeds onto the `Speed` type. 0.10
> corrected two interpolation methods that returned wrong values and an inverse
> conversion that was not the inverse of the forward one. See
> [CHANGELOG.md](CHANGELOG.md) for migration tables.

## Quick start

```rust
use bearingpro::navigation_solutions::{
    convert_compass_course_to_true_course, convert_true_course_to_compass_course,
};
use bearingpro::{CompassCourse, DeviationTable, InterpolationMethod, NavigationError, Variation};

fn main() -> Result<(), NavigationError> {
    // A swing: deviation observed on every tenth of the compass, 000° to 350°.
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9,      // 000°..080°
        0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2,      // 090°..170°
        -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, // 180°..260°
        -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,  // 270°..350°
    ])?;

    let variation = Variation::new(-2.7)?; // 2.7° west

    // Steering 003° by the compass — what are we actually making good?
    let solution = convert_compass_course_to_true_course(
        CompassCourse::new(3.0)?,
        variation,
        &table,
        InterpolationMethod::Cubic,
    )?;

    assert_eq!(format!("{}", solution.course), "358.2°T");
    assert_eq!(format!("{:.4}", solution.deviation.degrees()), "-2.0665");

    // And back again.
    let back = convert_true_course_to_compass_course(
        solution.course,
        variation,
        &table,
        InterpolationMethod::Cubic,
    )?;
    assert!((back.course.degrees() - 3.0).abs() < 1e-9);

    Ok(())
}
```

## Angles carry their frame

Every angle is a newtype tagged with the reference frame it is measured from.
Mixing frames does not compile:

```rust,compile_fail
use bearingpro::navigation_solutions::magnetic_to_true;
use bearingpro::{NavigationError, TrueCourse, Variation};

fn main() -> Result<(), NavigationError> {
    let true_course = TrueCourse::new(90.0)?;
    let variation = Variation::new(-3.0)?;

    // `magnetic_to_true` takes a MagneticCourse. This is a compile error rather
    // than a plausible-looking wrong answer.
    let _ = magnetic_to_true(true_course, variation);
    Ok(())
}
```

The types also carry their range invariant — a direction is always finite and
always in `[0°, 360°)` — which is why the corrections that only add or subtract a
known angle return a value rather than a `Result`:

```rust
use bearingpro::navigation_solutions::{compass_to_magnetic, magnetic_to_true};
use bearingpro::{CompassCourse, Deviation, NavigationError, Variation};

fn main() -> Result<(), NavigationError> {
    let compass = CompassCourse::new(357.0)?;
    let deviation = Deviation::new(5.5)?;
    let variation = Variation::new(-2.0)?;

    // No `?` on these two: they cannot fail.
    let magnetic = compass_to_magnetic(compass, deviation);
    let true_course = magnetic_to_true(magnetic, variation);

    assert_eq!(format!("{}", magnetic), "002.5°M");
    assert_eq!(format!("{}", true_course), "000.5°T");

    // Out-of-range and non-finite input is rejected at construction instead.
    assert!(CompassCourse::new(400.0).is_err());
    assert!(Variation::new(f64::NAN).is_err());

    // ...and `wrap` is there for when wrapping is what you actually mean.
    assert_eq!(CompassCourse::wrap(-10.0)?.degrees(), 350.0);
    Ok(())
}
```

| Type | Meaning | Range |
|---|---|---|
| `CompassCourse` / `CompassBearing` | as read from the ship's compass | `[0°, 360°)` |
| `MagneticCourse` / `MagneticBearing` | referred to magnetic north | `[0°, 360°)` |
| `TrueCourse` / `TrueBearing` | referred to true north | `[0°, 360°)` |
| `GyroCourse` / `GyroBearing` | as read from the gyrocompass | `[0°, 360°)` |
| `Variation` | true north to magnetic north, east positive | `[-180°, 180°]` |
| `Deviation` | magnetic north to compass north, east positive | `[-180°, 180°]` |
| `RelativeBearing` | clockwise from the ship's head | `[0°, 360°)` |
| `Angle` | a plain angular magnitude: gyro error, sextant angle, leeway | any finite |
| `Latitude` / `Longitude` | position, north and east positive | `[-90°, 90°]` / `[-180°, 180°)` |
| `Distance` / `Speed` | stored in nautical miles and knots | any finite |

Within one frame a course and a bearing are the same quantity and share a type.
What the types prevent is mixing *frames*, which is the mistake that puts a ship
aground.

The gyrocompass gets its own frame because its error is a different animal from
magnetic deviation — one number, not a curve, but one that depends on the ship's
own speed:

```rust
use bearingpro::navigation_solutions::{gyro_error_from_transit, gyro_speed_error, gyro_to_true};
use bearingpro::{GyroBearing, Latitude, NavigationError, Speed, TrueBearing, TrueCourse};

fn main() -> Result<(), NavigationError> {
    // Twenty knots due north in latitude 60°: the meridian is dragged west.
    let speed_error = gyro_speed_error(
        Latitude::from_degrees(60.0)?,
        TrueCourse::new(0.0)?,
        Speed::from_knots(20.0)?,
    )?;
    assert_eq!(format!("{speed_error:.2}"), "-2.54°");

    // And the total error, checked against a transit of known direction.
    let observed = GyroBearing::new(46.5)?;
    let charted = TrueBearing::new(45.0)?;
    let error = gyro_error_from_transit(observed, charted);
    assert_eq!(format!("{error:.1}"), "-1.5°");
    assert_eq!(gyro_to_true(observed, error).degrees(), 45.0);
    Ok(())
}
```

## Positions and the sailings

```rust
use bearingpro::sailings::{cross_track, geodesic, great_circle, great_circle_vertex, rhumb_line};
use bearingpro::{NavigationError, Position, TrackSide};

fn main() -> Result<(), NavigationError> {
    // The Lizard to Cape Race.
    let from = Position::from_degrees(49.95, -5.20)?;
    let to = Position::from_degrees(46.66, -53.07)?;

    // One course the whole way, or the shortest track?
    let steered = rhumb_line(from, to)?;
    let direct = great_circle(from, to)?;

    assert_eq!(format!("{:.1}", steered.distance.nautical_miles()), "1921.0");
    assert_eq!(format!("{:.1}", direct.distance.nautical_miles()), "1889.1");

    // The rhumb line holds one course; the great circle does not.
    assert_eq!(format!("{:.1}", steered.initial_course.degrees()), "264.1");
    assert_eq!(format!("{:.1}", direct.initial_course.degrees()), "282.8");
    assert_eq!(format!("{:.1}", direct.final_course.degrees()), "246.1");

    // Its highest latitude, which is what limits a winter passage.
    let vertex = great_circle_vertex(from, direct.initial_course)?;
    assert_eq!(format!("{vertex}"), "51°08.1'N 021°43.1'W");

    // On the ellipsoid the same track is a little longer.
    assert_eq!(format!("{:.1}", geodesic(from, to)?.distance.nautical_miles()), "1894.6");

    // How far off the great-circle track are we, and how much is left to run?
    let ship = Position::from_degrees(48.5, -30.0)?;
    let off = cross_track(ship, from, to)?;
    assert_eq!(off.side, TrackSide::Port);
    assert_eq!(format!("{:.1}", off.distance.nautical_miles()), "139.7");
    assert_eq!(format!("{:.0}", off.to_run.nautical_miles()), "927");
    Ok(())
}
```

Distances and speeds are types too, so the unit is never in doubt:

```rust
use bearingpro::{Distance, NavigationError, Speed};
use core::time::Duration;

fn main() -> Result<(), NavigationError> {
    let leg = Distance::from_nautical_miles(12.0)?;
    assert_eq!(format!("{:.0}", leg.metres()), "22224");
    assert_eq!(format!("{:.0}", leg.cables()), "120");

    let speed = Speed::from_knots(8.0)?;
    assert_eq!(speed.time_to_cover(leg)?, Duration::from_secs(5400));
    assert_eq!(speed.distance_covered(Duration::from_secs(3600)).nautical_miles(), 8.0);
    Ok(())
}
```

Positions are read from the forms they are written in, and print the same way:

```rust
use bearingpro::{Latitude, NavigationError, Position};

fn main() -> Result<(), NavigationError> {
    let expected = Position::from_degrees(50.755, -1.2966667)?;

    for text in [
        "50°45.3'N 001°17.8'W",
        "50 45.3 N 001 17.8 W",
        "N50°45.3' W001°17.8'",
        "50.755, -1.2966667",
    ] {
        let position: Position = text.parse()?;
        assert!(position.latitude().degrees() - expected.latitude().degrees() < 1e-6);
    }

    assert_eq!(format!("{expected}"), "50°45.3'N 001°17.8'W");

    // Seconds work too, and a hemisphere that does not belong is refused.
    assert_eq!("50°45'18\"N".parse::<Latitude>()?.degrees(), 50.755);
    assert!("50°45.3'E".parse::<Latitude>().is_err());
    assert!("50 60.0 N".parse::<Latitude>().is_err()); // sixty minutes is the next degree
    Ok(())
}
```

## Passage planning

```rust
use bearingpro::route::{LegKind, Route};
use bearingpro::sailings::TrackSide;
use bearingpro::{Distance, NavigationError, Position, Speed};

fn main() -> Result<(), NavigationError> {
    let route = Route::new(
        vec![
            "50°06.0'N 001°30.0'W".parse::<Position>()?,
            "49°54.0'N 002°00.0'W".parse::<Position>()?,
            "49°42.0'N 002°45.0'W".parse::<Position>()?,
        ],
        LegKind::RhumbLine,
    )?;

    assert_eq!(route.leg_count(), 2);
    assert_eq!(format!("{:.1}", route.total_distance()?.nautical_miles()), "54.2");
    assert_eq!(route.passage_time(Speed::from_knots(10.0)?)?.as_secs() / 60, 325);

    // Underway: which leg are we on, how far off it, and how much is left?
    let progress = route.progress("50°00.0'N 001°43.0'W".parse::<Position>()?)?;
    assert_eq!(progress.leg, 0);
    assert_eq!(progress.cross_track.side, TrackSide::Port);
    assert_eq!(format!("{:.1}", progress.cross_track.distance.nautical_miles()), "0.7");
    assert_eq!(format!("{:.0}", progress.distance_to_end.nautical_miles()), "44");

    // A great-circle route, broken into legs a ship can actually steer.
    let ocean = Route::new(
        vec![
            Position::from_degrees(49.95, -5.20)?,
            Position::from_degrees(46.66, -53.07)?,
        ],
        LegKind::GreatCircle,
    )?;
    let steerable = ocean.split_legs(Distance::from_nautical_miles(300.0)?)?;
    assert_eq!(steerable.kind(), LegKind::RhumbLine);
    for leg in steerable.legs()? {
        assert!(leg.sailing.distance.nautical_miles() <= 300.0);
    }
    Ok(())
}
```

## Dead reckoning

```rust
use bearingpro::dead_reckoning::{dead_reckoning, estimated_position};
use bearingpro::navigation_solutions::Current;
use bearingpro::{NavigationError, Position, Speed, TrueCourse};
use core::time::Duration;

fn main() -> Result<(), NavigationError> {
    let noon = Position::from_degrees(50.0, -5.0)?;
    let heading = TrueCourse::new(270.0)?;
    let speed = Speed::from_knots(12.0)?;
    let watch = Duration::from_secs(4 * 3600);

    // Course and distance alone.
    let reckoned = dead_reckoning(noon, heading, speed, watch)?;
    assert_eq!(format!("{reckoned}"), "50°00.0'N 006°14.6'W");

    // Allowing for a knot of north-going stream.
    let current = Current {
        set: TrueCourse::new(0.0)?,
        drift: Speed::from_knots(1.0)?,
    };
    let estimated = estimated_position(noon, heading, speed, current, watch)?;

    assert_eq!(format!("{}", estimated.position), "50°04.0'N 006°14.7'W");
    assert_eq!(format!("{:.1}", estimated.track.course_over_ground.degrees()), "274.8");
    assert_eq!(format!("{:.2}", estimated.track.speed_over_ground.knots()), "12.04");
    Ok(())
}
```

## Fixing the position

Three bearings, one of them three degrees out — the cocked hat opens up and the
residual says so:

```rust
use bearingpro::fix::{bearing_fix, cocked_hat, PositionLine};
use bearingpro::{NavigationError, Position, TrueBearing};

fn main() -> Result<(), NavigationError> {
    let lighthouse = Position::from_degrees(50.20, -4.00)?;
    let headland = Position::from_degrees(50.20, -4.40)?;
    let buoy = Position::from_degrees(49.95, -4.15)?;

    let good = [
        PositionLine::from_bearing_of(lighthouse, TrueBearing::new(52.0)?),
        PositionLine::from_bearing_of(headland, TrueBearing::new(308.0)?),
        PositionLine::from_bearing_of(buoy, TrueBearing::new(167.9)?),
    ];
    let fix = bearing_fix(&good)?;
    assert_eq!(format!("{}", fix.position), "50°06.0'N 004°12.0'W");
    assert!(fix.rms_residual.nautical_miles() < 0.01);

    // Now spoil the third bearing.
    let mut spoiled = good;
    spoiled[2] = PositionLine::from_bearing_of(buoy, TrueBearing::new(170.9)?);

    let hat = cocked_hat(spoiled)?;
    assert_eq!(format!("{:.2}", hat.greatest_side.nautical_miles()), "0.78");
    assert!(bearing_fix(&spoiled)?.rms_residual.nautical_miles() > 0.1);
    Ok(())
}
```

Distance off, without a range finder:

```rust
use bearingpro::fix::{dipping_distance, distance_by_two_bearings, distance_by_vertical_angle};
use bearingpro::{Angle, Distance, NavigationError, RelativeBearing};

fn main() -> Result<(), NavigationError> {
    // A light 80 m high subtending half a degree.
    let by_sextant = distance_by_vertical_angle(
        Distance::from_metres(80.0)?,
        Angle::from_minutes(30.0)?,
    )?;
    assert_eq!(format!("{by_sextant:.2}"), "4.95 M");

    // Doubling the angle on the bow: the run gives the distance off.
    let by_bearings = distance_by_two_bearings(
        RelativeBearing::new(30.0)?,
        RelativeBearing::new(60.0)?,
        Distance::from_nautical_miles(6.0)?,
    )?;
    assert_eq!(format!("{:.2}", by_bearings.at_second_bearing.nautical_miles()), "6.00");
    assert_eq!(format!("{:.2}", by_bearings.abeam.nautical_miles()), "5.20");

    // A 100 m light seen from a bridge 10 m up rises at 27.4 miles.
    let rising = dipping_distance(Distance::from_metres(10.0)?, Distance::from_metres(100.0)?)?;
    assert_eq!(format!("{rising:.2}"), "27.38 M");
    Ok(())
}
```

## Collision avoidance

```rust
use bearingpro::relative_motion::{
    closest_point_of_approach, course_for_cpa, Approach, Contact, Vessel,
};
use bearingpro::{Distance, NavigationError, Speed, TrueBearing, TrueCourse};

fn main() -> Result<(), NavigationError> {
    let own = Vessel {
        course: TrueCourse::new(0.0)?,
        speed: Speed::from_knots(15.0)?,
    };
    // Fine on the starboard bow at nine miles, coming the other way.
    let contact = Contact {
        bearing: TrueBearing::new(15.0)?,
        range: Distance::from_nautical_miles(9.0)?,
    };
    let target = Vessel {
        course: TrueCourse::new(200.0)?,
        speed: Speed::from_knots(12.0)?,
    };

    let Approach::Closing(cpa) = closest_point_of_approach(own, contact, target)? else {
        panic!("she is closing");
    };
    assert_eq!(format!("{:.2}", cpa.distance.nautical_miles()), "0.96");
    assert_eq!(format!("{:.0}", cpa.time_to_go.as_secs_f64() / 60.0), "20");

    // Two miles would be more comfortable. What course gives it?
    let avoidance = course_for_cpa(own, contact, target, Distance::from_nautical_miles(2.0)?)?;
    let starboard = avoidance.starboard.expect("an alteration to starboard exists");
    assert_eq!(format!("{:.1}", starboard.degrees()), "34.1");

    // And it really does: the answer is checked, not asserted.
    let after = closest_point_of_approach(
        Vessel { course: starboard, speed: own.speed },
        contact,
        target,
    )?;
    let Approach::Closing(after) = after else {
        panic!("still closing, just further off");
    };
    assert!((after.distance.nautical_miles() - 2.0).abs() < 1e-9);
    Ok(())
}
```

## Deviation tables

A table can be built from a full swing, from an arbitrary set of headings, or at
a fixed spacing:

```rust
use bearingpro::{DeviationTable, NavigationError};

fn main() -> Result<(), NavigationError> {
    // 36 values, 000° to 350°.
    let _swing = DeviationTable::from_deviation_vec(vec![0.0; 36])?;

    // Arbitrary headings. Negative and over-360 courses normalise properly.
    let _sparse = DeviationTable::from_vec(vec![(0, -2.5), (-270, 1.0), (180, 0.4)])?;

    // A fixed step, or the eight cardinal points.
    let _every_ten = DeviationTable::from_step(10)?;
    let _cardinal = DeviationTable::from_cardinal_directions();

    // Bad input is rejected rather than silently patched up.
    assert!(DeviationTable::from_step(0).is_err());       // used to abort the process
    assert!(DeviationTable::from_vec(vec![]).is_err());   // used to panic on first use
    assert!(DeviationTable::from_deviation_vec(vec![0.0; 12]).is_err()); // used to zero-fill
    Ok(())
}
```

Or, most usefully, from the swing itself. Deviation is never measured directly:
what is measured is a bearing of something whose true direction is known, taken
by the compass on each heading in turn.

```rust
use bearingpro::{
    CompassBearing, CompassCourse, DeviationTable, NavigationError, SwingObservation,
    TrueBearing, Variation,
};

fn main() -> Result<(), NavigationError> {
    let variation = Variation::new(-2.0)?;
    let transit = TrueBearing::new(45.0)?; // charted direction of the transit

    let observations = [(0.0, 48.5), (90.0, 46.0), (180.0, 45.5), (270.0, 48.0)]
        .into_iter()
        .map(|(heading, observed)| {
            Ok(SwingObservation {
                compass_heading: CompassCourse::new(heading)?,
                observed_bearing: CompassBearing::new(observed)?,
                reference_bearing: transit,
            })
        })
        .collect::<Result<Vec<_>, NavigationError>>()?;

    let table = DeviationTable::from_swing(&observations, variation)?;

    // On north the compass called the transit 048.5 when it is really 045.0,
    // with 2°W variation: deviation is 045.0 − (−2.0) − 048.5 = −1.5°.
    assert_eq!(table.deviation_at_node(0).unwrap().degrees(), -1.5);
    assert_eq!(table.deviation_at_node(90).unwrap().degrees(), 1.0);
    Ok(())
}
```

### Interpolation

| Method | Continuity | Nodes needed | Use when |
|---|---|---|---|
| `Linear` (default) | C⁰ | 2 | you want a value that can never overshoot the tabulated ones |
| `ShapePreserving` | C¹ | 2 | you want a smooth curve that still cannot overshoot |
| `Cubic` | C² | 3 | the swing is dense and you want the smoothest curve |
| `Parametric` | analytic | 5 | you want the classical A–E model, or want to smooth a noisy swing |

A cubic spline buys its second derivative by allowing the curve to bulge past the
data. On a swing with an abrupt step that puts the interpolated deviation outside
anything ever observed; `ShapePreserving` — the Fritsch–Carlson method — gives up
a little smoothness and cannot do it:

```rust
use bearingpro::{DeviationTable, InterpolationMethod, NavigationError};

fn main() -> Result<(), NavigationError> {
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9,
        0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2,
        -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9,
        -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
    ])?;

    // Between the 270° node (−19.2) and the 280° node (−18.1) the spline dips to
    // −20.3, a deviation this compass was never observed to have.
    let course = 273.0;
    let spline = table.deviation_at(course, InterpolationMethod::Cubic, None)?;
    let shaped = table.deviation_at(course, InterpolationMethod::ShapePreserving, None)?;

    assert_eq!(format!("{:.2}", spline.degrees()), "-20.31");
    assert_eq!(format!("{:.2}", shaped.degrees()), "-19.09");

    // The shape-preserving curve stays between the two nodes, as it must.
    assert!(shaped.degrees() >= -19.2 && shaped.degrees() <= -18.1);
    Ok(())
}
```

All four are **periodic**. The arc from the last node through 360°/0° back to
the first is a real interval, not a flat extrapolation:

```rust
use bearingpro::{DeviationTable, InterpolationMethod, NavigationError};

fn main() -> Result<(), NavigationError> {
    let mut table = DeviationTable::from_step(10)?;
    table.set_deviation(350, 10.0)?;
    table.set_deviation(0, -10.0)?;

    // Halfway round the 350°->000° arc, the deviation is halfway between.
    let midpoint = table.deviation_at(355.0, InterpolationMethod::Linear, None)?;
    assert!(midpoint.degrees().abs() < 1e-12);
    Ok(())
}
```

`Parametric` fits

```text
δ = A + B·sin(y) + C·cos(y) + D·sin(2y) + E·cos(2y)
```

by least squares. Any coefficient you supply is held fixed and the rest are
fitted around it:

```rust
use bearingpro::{DeviationCoefficients, DeviationTable, InterpolationMethod, NavigationError};

fn main() -> Result<(), NavigationError> {
    // A swing that is exactly 5°·sin(course).
    let values: Vec<f64> = (0..36)
        .map(|index| 5.0 * (f64::from(index) * 10.0).to_radians().sin())
        .collect();
    let table = DeviationTable::from_deviation_vec(values)?;

    let fitted = table.deviation_at(90.0, InterpolationMethod::Parametric, None)?;
    assert!((fitted.degrees() - 5.0).abs() < 1e-9);

    // Hold the constant term at 1° and fit B..E around it.
    let coefficients = DeviationCoefficients { a: Some(1.0), ..Default::default() };
    let pinned = table.deviation_at(
        90.0,
        InterpolationMethod::Parametric,
        Some(&coefficients),
    )?;
    assert!((pinned.degrees() - 6.0).abs() < 1e-9);
    Ok(())
}
```

## The inverse problem

Deviation is tabulated against the **compass** course, so converting a true
course back to a compass course means solving

```text
CC + δ(CC) = MC
```

for `CC` — an implicit equation, not a subtraction. `bearingpro` solves it, so
the two directions agree to the solver's tolerance:

```rust
use bearingpro::navigation_solutions::{
    convert_compass_course_to_true_course, convert_true_course_to_compass_course,
};
use bearingpro::{
    CompassCourse, DeviationTable, InterpolationMethod, NavigationError, SmithCoefficients,
    Variation,
};

fn main() -> Result<(), NavigationError> {
    // A smooth, well-behaved swing.
    let model = SmithCoefficients { a: 2.0, b: 3.0, c: -4.0, d: 1.5, e: -0.5 };
    let values: Vec<f64> = (0..36)
        .map(|index| model.deviation_at(f64::from(index) * 10.0))
        .collect();
    let table = DeviationTable::from_deviation_vec(values)?;
    let variation = Variation::new(-2.7)?;

    let mut worst: f64 = 0.0;
    let mut course = 0.0;
    while course < 360.0 {
        let compass = CompassCourse::new(course)?;
        let out = convert_compass_course_to_true_course(
            compass, variation, &table, InterpolationMethod::Cubic,
        )?;
        let back = convert_true_course_to_compass_course(
            out.course, variation, &table, InterpolationMethod::Cubic,
        )?;
        worst = worst.max(back.course.angular_distance(compass));
        course += 0.5;
    }

    assert!(worst < 1e-8, "worst round-trip error was {worst}");
    Ok(())
}
```

### When a swing cannot be inverted

If deviation changes by more than a degree for each degree of heading, two
compass courses produce the same magnetic course, and the question "what compass
course gives this true course" stops having one answer. The library detects that
rather than quietly picking one:

```rust
use bearingpro::navigation_solutions::convert_true_course_to_compass_course;
use bearingpro::{DeviationTable, InterpolationMethod, NavigationError, TrueCourse, Variation};

fn main() -> Result<(), NavigationError> {
    // This sample swing jumps 12.5° between 230° and 240°.
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9,
        0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2,
        -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9,
        -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
    ])?;

    assert!(!table.is_invertible());
    assert!((table.max_slope() - 1.99).abs() < 0.01); // degrees of δ per degree of heading

    let solution = convert_true_course_to_compass_course(
        TrueCourse::new(256.0)?,
        Variation::new(0.7)?,
        &table,
        InterpolationMethod::Linear,
    )?;

    // The answer is still correct — steering it does make 256°T good — but the
    // advisory says it is not the only compass course that would.
    assert_eq!(format!("{:.2}", solution.course.degrees()), "274.05");
    assert!(solution.advisories.non_invertible_table);
    Ok(())
}
```

## Analysing a swing

```rust
use bearingpro::{DeviationTable, NavigationError};

fn main() -> Result<(), NavigationError> {
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9,
        0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2,
        -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9,
        -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
    ])?;

    let analysis = table.analyze()?;

    assert_eq!(format!("{:.4}", analysis.coefficients.a), "-2.4083");
    assert_eq!(format!("{:.4}", analysis.coefficients.b), "4.5557");
    assert_eq!(analysis.nodes, 36);
    assert_eq!(format!("{:.1}", analysis.max_gap), "10.0");

    // An RMS residual this large means the classical five-coefficient model does
    // not describe this compass — which, for a swing with a 12.5° step in it, is
    // exactly the right conclusion.
    assert!(analysis.rms_residual > 4.0);
    Ok(())
}
```

## The current triangle

```rust
use bearingpro::navigation_solutions::{course_over_ground, course_to_steer, estimate_current};
use bearingpro::{NavigationError, Speed, TrueCourse};

fn main() -> Result<(), NavigationError> {
    let heading = TrueCourse::new(0.0)?; // steering due north
    let set = TrueCourse::new(90.0)?;    // current setting due east
    let speed = Speed::from_knots(10.0)?;
    let drift = Speed::from_knots(2.0)?;

    // What are we making good?
    let track = course_over_ground(heading, speed, set, drift)?;
    assert_eq!(format!("{:.2}", track.course_over_ground.degrees()), "11.31");
    assert_eq!(format!("{:.2}", track.speed_over_ground.knots()), "10.20");

    // What should we steer to make good due north instead?
    let steering = course_to_steer(TrueCourse::new(0.0)?, speed, set, drift)?;
    assert_eq!(format!("{:.2}", steering.heading.degrees()), "348.46");
    assert_eq!(format!("{:.2}", steering.speed_over_ground.knots()), "9.80");

    // What current explains the difference between water track and ground track?
    let current = estimate_current(
        heading,
        speed,
        track.course_over_ground,
        track.speed_over_ground,
    )?;
    assert!(current.set.angular_distance(set) < 1e-9);
    assert!((current.drift.knots() - drift.knots()).abs() < 1e-9);

    // A current the ship cannot outrun is reported, not approximated.
    assert!(course_to_steer(
        TrueCourse::new(0.0)?,
        Speed::from_knots(2.0)?,
        set,
        Speed::from_knots(10.0)?,
    )
    .is_err());
    Ok(())
}
```

## Advisories and error estimates

Every conversion returns the numbers that went into it, an estimate of the
interpolation uncertainty, and a set of advisories with documented thresholds:

```rust
use bearingpro::navigation_solutions::convert_compass_course_to_true_course;
use bearingpro::{CompassCourse, DeviationTable, InterpolationMethod, NavigationError, Variation};

fn main() -> Result<(), NavigationError> {
    let table = DeviationTable::from_deviation_vec(vec![
        -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9,
        0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2,
        -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9,
        -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
    ])?;

    let solution = convert_compass_course_to_true_course(
        CompassCourse::new(270.0)?,
        Variation::new(-20.0)?,
        &table,
        InterpolationMethod::Linear,
    )?;

    assert!(solution.advisories.large_variation);      // |variation| > 15°
    assert!(solution.advisories.large_deviation);      // |deviation| > 10°
    assert!(solution.advisories.non_invertible_table); // δ changes faster than 1°/1°
    assert!(!solution.advisories.coarse_table);        // widest node gap > 45°
    assert!(solution.check_data_required());

    // Estimated interpolation uncertainty, in degrees.
    assert!(solution.estimated_error.is_finite());
    Ok(())
}
```

`estimated_error` is the classical interpolation error bound for `Linear` and
`Cubic`, and the RMS residual of the fit for `Parametric`. It describes the
interpolation only; it cannot know how well the swing itself was observed.

## Errors

There is one error type, `NavigationError`. It is `#[non_exhaustive]`, so match
it with a wildcard arm.

```rust
use bearingpro::{CompassCourse, DeviationTable, NavigationError};

fn main() {
    let error = DeviationTable::from_step(0).unwrap_err();
    assert_eq!(error, NavigationError::InvalidStep { step: 0 });
    assert_eq!(
        error.to_string(),
        "invalid deviation table step: 0. Must be between 1 and 180 degrees"
    );

    match CompassCourse::new(400.0) {
        Err(NavigationError::OutOfRange { value, max, .. }) => {
            assert_eq!(value, 400.0);
            assert_eq!(max, 360.0);
        }
        _ => panic!("400° is out of range"),
    }
}
```

Nothing in this crate panics on caller-supplied data. `NaN`, infinities,
degenerate tables and extreme magnitudes all come back as an error. That is
enforced at compile time — `clippy::unwrap_used`, `expect_used`, `panic` and
`indexing_slicing` are denied, and `unsafe_code` is forbidden — and tested by
sweeping the public API with hostile input in `tests/robustness.rs`. See
[SECURITY.md](SECURITY.md).

## Storing and sending

With the `serde` feature the value types serialise and deserialise — and
deserialisation goes through the same validation as construction, so a stored
file cannot smuggle in a latitude of 500° or a deviation table with two entries
for the same heading:

```toml
bearingpro = { version = "0.12", features = ["serde"] }
```

```rust,ignore
let route: Route = serde_json::from_str(&plan)?;      // checked on the way in
assert!(serde_json::from_str::<Latitude>("500.0").is_err());
assert!(serde_json::from_str::<DeviationTable>("[]").is_err());
```

## `no_std`

```toml
bearingpro = { version = "0.10", default-features = false, features = ["libm"] }
```

`alloc` is required. CI builds the crate for `thumbv7em-none-eabihf` on every
commit, so the `no_std` support is checked rather than claimed.

## Which model is used where

Navigation is full of models that agree to three figures and differ in the
fourth, so each function says which one it uses:

| Computation | Model |
|---|---|
| [`sailings::rhumb_line`], [`sailings::great_circle`] | sphere of mean radius 6371.0088 km |
| [`sailings::geodesic`] | WGS-84 ellipsoid, Vincenty |
| [`Latitude::meridional_parts`] | WGS-84 ellipsoid |
| Position lines and their crossings | rhumb lines, exact on a Mercator chart |
| Bearing fixes | least squares in Mercator coordinates |
| Range fixes | azimuthal equidistant plane about the observer |
| Relative motion | plane |

[`sailings::rhumb_line`]: https://docs.rs/bearingpro/latest/bearingpro/sailings/fn.rhumb_line.html
[`sailings::great_circle`]: https://docs.rs/bearingpro/latest/bearingpro/sailings/fn.great_circle.html
[`sailings::geodesic`]: https://docs.rs/bearingpro/latest/bearingpro/sailings/fn.geodesic.html
[`Latitude::meridional_parts`]: https://docs.rs/bearingpro/latest/bearingpro/position/struct.Latitude.html#method.meridional_parts

## Roadmap

Not implemented yet, in rough order of usefulness:

- NMEA 0183 parsing and generation (`HDG`, `HDM`, `HDT`, `VHW`, `RMC`, `VTG`),
  behind a feature flag. This is the one place undertrusted data would enter the
  library, so it wants a fuzz target alongside it rather than just a parser.
- Magnetic variation from the WMM or IGRF field model, instead of requiring it as
  an input. Deliberately not guessed at: the coefficient tables are safety
  relevant, expire every five years, and belong in the release that ships them.
- Tidal heights and streams: the rule of twelfths, secondary port corrections,
  rates between springs and neaps.
- Sun azimuth and amplitude, for checking a compass against a heavenly body —
  the small, useful slice of astronomical navigation.
- Weighted least squares and outlier detection for a swing, so one bad
  observation can be found rather than merely averaged in.
- Compass adjustment: what the A–E coefficients say about correctors, magnets and
  the Flinders bar.

## License

MIT. See [LICENSE](LICENSE).
