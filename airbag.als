open util/ordering[Time] as T

sig Time {}

sig Speed{
	value: Int
}

-- ziroskop, sa vrednosti koju izmeri (promena gravitacione sile)
sig Gyroscope {
	g_meter: Int
}

-- ogranicenje vrednosti za g_meter
pred gyro_val {
	all g: Gyroscope | g.g_meter >= 0 and g.g_meter <= 30
}

-- TODO: definisati kocnicu i ogranicenje da uvek vazi da jacina pritiska mora da bude izmedju 0 i 1 
-- (odnosno, predstaviti kao 0 -100)
-- nakon toga, dodati kocnicu na sva mesta gde je potrebno

abstract sig Sensor {
}

sig ImpactSensor, SideSensor, SeatWeightSensor, SeatbeltSensor extends Sensor {}

abstract sig Switch {
	on: set Time
}

abstract sig AirbagPosition {}
sig Normal, Knee extends AirbagPosition {}

sig AirbagSwitch extends Switch {}

sig ACUSensors {
	speed: Speed one -> Time,
	gyro: Gyroscope one -> Time,
	frontal: ImpactSensor one -> Time,
	side: SideSensor one -> Time
}

some sig Airbag {
	on: set Time,
	activated: set Time, 
	seatbelt: SeatbeltSensor one -> Time,
	weight: SeatWeightSensor one -> Time,
	switch: AirbagSwitch one -> Time, 
	sensors: ACUSensors one -> Time,
	position: AirbagPosition
}

-- samo "ukljucivanje" u smislu da je airbag u stanju pripravnosti
-- aktivacija se naknadno može desiti jedino ukoliko je airbag "ukljucen"
pred turn_on [a: Airbag, t, t': Time ] { 
	-- precondition: airbag is off
	!is_on[a, t]
	-- postcondition: airbag is on
	is_on[a, t']
}

-- TODO: iskljucivanje
-- dodati ga i kasnije gde je potrebno


-- aktivacija jednog airbag-a
pred activate[a: Airbag, t, t': Time] {
	-- preconditions
	is_on[a, t] 
	are_conditions_ok[a, t]

	-- postcondition
	is_activated[a, t]
	-- frame condition
	activated_changes[Airbag - a, t, t']
}

pred still_impact [a: Airbag, t, t': Time] {
	-- precondition
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value < 3) and 
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t) and
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter >= 2)
			
	-- postcondition
	activate[a, t, t']
}

-- TODO: udarac u slucaju vece brzine
pred speed_impact [a: Airbag, t, t': Time] {

}

-- TODO: ne zaboraviti i proveru da noga nije jako pritisnuta na kocnici
pred speed_impact_knee [a: Airbag, t, t': Time] {
	
}


pred is_on [a: Airbag, t: Time] {
	t in a.on and one a.switch :> t
}

pred is_activated[a: Airbag, t: Time] {
	t in a.activated
}

pred are_conditions_ok[a: Airbag, t:Time] {
	one a.switch :> t and one a.seatbelt :> t and one a.weight :> t
}

pred activated_changes[A: set Airbag, t,t': Time] {
	all a: A |
		-- TODO: ukljuciti uslove sa senzora tezine, o vezanom pojasu i korisnickom prekidacu
		t' in a.activated iff t in a.on
}

-- TODO: predikat "transitions"

-- airbag 1: normal

one sig A1 extends Airbag {}
one sig TNOR extends Normal {}
one sig ABS1 extends AirbagSwitch {}
one sig SWS1 extends SeatWeightSensor {}
one sig SBS1 extends SeatbeltSensor {}

-- ACU

one sig ACU1 extends ACUSensors{}
one sig G1 extends Gyroscope {}
one sig IS1 extends ImpactSensor {}
one sig DS1 extends SideSensor {}

one sig S1 extends Speed {}

-- TODO: dodati airbag za kolena i potrebne komponente

fact {
	G1.g_meter = 0
}

pred init [t: Time] {
	-- TODO: dopuniti init podacima za airbag za kolena
	A1.position = TNOR
	A1.sensors.t = ACU1
	A1.weight.t = SWS1
	A1.seatbelt.t = SBS1
	A1.switch.t = ABS1

	ACU1.speed.t = S1
	ACU1.gyro.t = G1
	ACU1.frontal.t = IS1
	ACU1.side.t = DS1	

 	!is_on[A1, t] and !is_activated[A1, t]
 	
	-- TODO: dopuniti uslovom da i za sve ostale airbag-ove u pocetku vazi da su iskljuceni
}

pred safety_check {
 some Airbag
 init [T/first]
 some t: Time | safe [t]
} 

pred safe [t: Time] {
  ACU1.gyro.t != G1
}

run safety_check for 4
