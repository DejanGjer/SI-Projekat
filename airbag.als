open util/ordering[Time] as T

sig Time {}

-- brzina, nisu postavljena neka ograničenja
sig Speed{
	value: Int
}

-- ziroskop, sa vrednosti koju izmeri (promena gravitacione sile)
sig Gyroscope {
	g_meter: Int
}

-- ogranicenje vrednosti za g_meter
-- postavljeno da bude fact jer važi svuda
fact gyro_val {
	-- za svaki žiroskop važi da može da izmeri vrednosti između 0 i 30G sile
	all g: Gyroscope | g.g_meter >= 0 and g.g_meter <= 30
}

-- TODO: definisati kocnicu i ogranicenje da uvek vazi da jacina pritiska mora da bude izmedju 0 i 1 
-- (odnosno, predstaviti kao 0 -100)
sig BrakePosition {
	pos: Int
}

-- ograničenje vrednosti za poziciju kočnice
-- postavljeno da bude fact jer važi svuda
fact pos_val {
	all b: BrakePosition | b.pos >=0 and b.pos <=100
}
-- nakon toga, dodati kocnicu na sva mesta gde je potrebno

abstract sig Sensor {
}

sig ImpactSensor, SideSensor, SeatWeightSensor, SeatbeltSensor extends Sensor {}

-- switch na airbag-u koji može da se isključi
-- npr. u slučaju da vozač ima dete koje vozi na prednjem sedištu
abstract sig Switch {
	on: set Time
}

--tip pozicije na kojoj se nalazi airbag
--Normal - za klasične pozicije
--Knee - za poziciju kod kolena vozača 
abstract sig AirbagPosition {}
sig Normal, Knee extends AirbagPosition {}

sig AirbagSwitch extends Switch {}

--Senzori sa ACU jedinice
sig ACUSensors {
	speed: Speed one -> Time,
	gyro: Gyroscope one -> Time,
	-- senzor za frontalni udarac
	frontal: ImpactSensor one -> Time,
	-- senzor za udarac sa strane
	side: SideSensor one -> Time,
	-- kocnica dodata
	brake_pos: BrakePosition one -> Time
}

--Tip podatka airbag
some sig Airbag {
	-- skup vremena kada je airbag uključen
	on: set Time,
	--skup vremena kada je airbag aktiviran
	activated: set Time, 
	--senzor za vezan pojas na odgovarajućem sedištu
	seatbelt: SeatbeltSensor one -> Time,
	--senzor težine na odgovarajućem sedištu
	weight: SeatWeightSensor one -> Time,
	switch: AirbagSwitch one -> Time, 
	--senzori sa ACU jedinice
	sensors: ACUSensors one -> Time,
	--tip pozicije airbag-a
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
pred turn_off [a: Airbag, t,t': Time] {
	-- preconditions  
	-- airbag is on
	is_on[a, t]

	-- postconditions  
	-- airbag is off
	!is_on[a, t']
}


-- aktivacija jednog airbag-a
pred activate[a: Airbag, t, t': Time] {
	-- preconditions
	is_on[a, t] 
	-- provera uslova neophodnih da bi se airbag aktivirao (sem postojanja udara - spoljasnji faktor)
	are_conditions_ok[a, t]

	-- postcondition
	is_activated[a, t']
	-- frame condition
	-- prolazimo i kroz sve ostale airbag-ove da se provere uslovi njihovih aktivacija
	activated_changes[Airbag - a, t, t']
}

-- predikat za udarac u mirovanju auta
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
	-- precondition
	(let s = a.sensors.t | 
	let speed = s.speed.t |
		speed.value >= 3) and 
	(let s = a.sensors.t | 
	some s.frontal :> t or some s.side :> t) and -- frontalni ili bocni senzor je detektovan
	(let s = a.sensors.t | 
	let gyro = s.gyro.t |
		gyro.g_meter > 3) -- ziroskop vise od 3G
			
	-- postcondition
	activate[a, t, t']
}

-- TODO: ne zaboraviti i proveru da noga nije jako pritisnuta na kocnici
-- prvobitna ideja je bila da uslovi budu isti kao za speed_impact i da se još doda uslov za kočnicu
-- pošto smatramo da ima smisla da i kod udarca u mirovanju može da se desi da vozač pritiska kočnicu
-- modifikovali smo predikat tako da proveravamo da li se desio still ili speed impact, i ako nešto od toga jeste
-- zahteva još i uslov za pritisak kočnice 
--stari kod je zakomentarisan  
pred impact_knee [a: Airbag, t, t': Time] {
	-- precondition
	--(let s = a.sensors.t | 
	--let speed = s.speed.t |
	--	speed.value >= 3) and 
	--(let s = a.sensors.t | 
	--some s.frontal :> t or some s.side :> t) and -- frontalni ili bocni senzor je detektovan
	--(let s = a.sensors.t | 
	--let gyro = s.gyro.t |
	--	gyro.g_meter > 3) and  -- ziroskop vise od 3G
	
	(let s = a.sensors.t |
	let b = s.brake_pos.t |
		b.pos <= 70) and
	(still_impact[a,t,t'] or speed_impact[a,t,t']) -- pozicija kocnice moze ici do 70, inace dolazi do povrede
			
}

pred is_on [a: Airbag, t: Time] {
	t in a.on and one a.switch :> t
}

pred is_activated[a: Airbag, t: Time] {
	t in a.activated
}

-- Uslovi koji moraju biti ispunjeni da bi se airbag aktivirao
pred are_conditions_ok[a: Airbag, t:Time] {
	-- switch mora biti uključen
	-- senzori za vezan pojas i težinu na sedištu moraju biti aktivni
	one a.switch :> t and one a.seatbelt :> t and one a.weight :> t
}

pred activated_changes[A: set Airbag, t,t': Time] {
	--prolazimo za svaki airbag
	all a: A |
		-- TODO: ukljuciti uslove sa senzora tezine, o vezanom pojasu i korisnickom prekidacu
		--aktiviramo trenutni airbag ako je:
		--1) uključen i ima ispunjene sve uslove
		--2) ako je airbag tipa Knee, onda proveravamo dadtni uslov za kočnicu (jer to nije provereno uslovom 1)
		t' in a.activated iff (t in a.on and are_conditions_ok[a, t] and (a.position = Normal or 
		(let s = a.sensors.t |
		let b = s.brake_pos.t |
		b.pos <= 70)))
}

-- TODO: predikat "transitions"
--definišemo moguće tranzicije u vremenu
--kod tranzicije moguće akcije za airbag su turn on i turn off i impacti
--ako je airbag tipa Normal možemo pozvati still_impact ili speed_impact
--a, ako je airbag tipa Knee onda možemo da pozovemo samo impact_knee
pred transitions[t,t': Time] {
  some a: Airbag |
    turn_on [a, t, t'] or
    turn_off [a, t, t'] or
    (a.position = Normal and (still_impact[a, t, t'] or
    speed_impact[a,t,t'])) or
    (a.position = Knee and impact_knee[a,t,t'])
}

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
-- kocnica
one sig BP1 extends BrakePosition{}

one sig S1 extends Speed {}

-- TODO: dodati airbag za kolena i potrebne komponente
--Komponente za drugi airbag
one sig A2 extends Airbag {}
one sig TKNEE extends Knee {}
one sig ABS2 extends AirbagSwitch {}
one sig SWS2 extends SeatWeightSensor {}
one sig SBS2 extends SeatbeltSensor {}

--početna vrednost žirometra
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

	-- podaci za airbag za koleno
	A2.position = TKNEE
	A2.sensors.t = ACU1
	A2.weight.t = SWS2
	A2.seatbelt.t = SBS2
	A2.switch.t = ABS2

	--podaci za ACU jedinicu
	ACU1.speed.t = S1
	ACU1.gyro.t = G1
	ACU1.frontal.t = IS1
	ACU1.side.t = DS1
	--kocnica
	ACU1.brake_pos.t = BP1

 	!is_on[A1, t] and !is_activated[A1, t]
 	
	-- TODO: dopuniti uslovom da i za sve ostale airbag-ove u pocetku vazi da su iskljuceni
	!is_on[A2, t] and !is_activated[A2, t]
}

pred safety_check {
 some Airbag
 init [T/first] 
 all t: Time - T/last | 
   	transitions [t, T/next[t]]
 some t: Time | safe [t]
} 

pred safe [t: Time] {
  -- dodat pored originalne verzije i uslov da se airbag A1 aktivirao, moze da se obrise posle posto sluzi samo za proveru
  ACU1.gyro.t != G1 and (t in A1.activated)
}

run safety_check for 2 but 8 int
