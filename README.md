Insert tracking code into rust fn

Example
---------------------------------------------------------------
```text
[track] main enter     at main.rs:48
[track] foo enter     at main.rs:38
[track] foo return'1  at main.rs:40 = Err(Missing)
[track] foo enter     at main.rs:38
[track] foo endret'0  at main.rs:45 = Ok(())
[track] foo enter     at main.rs:38
[track] foo return'2  at main.rs:43 = Err(Invalid)
[track] main endret'3  at main.rs:51 = ()
```
