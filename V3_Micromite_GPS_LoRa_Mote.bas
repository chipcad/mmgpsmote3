''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
'           Micromite_GPS_LoRa_Mote_3V1.bas
' Holman Tamas ChipCAD Kft.
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  OPTION EXPLICIT
  OPTION AUTORUN ON
  OPTION DEFAULT INTEGER
  CPU 10
  ? "Micromite GPS LoRa Mote 3v1 March 22 2017"
' Reset click modules
  CONST FORCE=2                               'digital O
  CONST GPSPWR=3                              'digital O
  CONST PGD=4                                 'digital O to switch T2 or digital/analog I/O
  CONST PGC=5                                 'digital O to switch T3 or digital/analog I/O
  CONST LVP=6                                 'digital/analog I/O
  CONST BATT=7                                'analog in
  CONST SELA=9                                'digital O
  CONST SELB=10                               'digital O
  CONST LEDG=14                               'digital O
  CONST LEDR=15                               'digital O     
  CONST WAKEUP=16                             'digital I
  CONST SDA=17                                'digital O or SCL I2C
  CONST SCL=18                                'digital O or SDA I2C
  CONST TX1=21                                'digital O or TX1
  CONST RX1=22                                'digital O or RX1
  CONST RNReset=23                            'digital O or RNReset
  CONST PUSH=25                               'digital I
  CONST PPS=26                                'digital I
  CONST LEDON=0,LEDOFF=1
  CONST MaxTime=360                           '360 seconds maximum GPS operation time without motion detection 
  CONST GPSFullOperationTime=300              '300 seconds in full on mode
  CONST CO2OperatingTime=1500                 'millisecond
  CONST MCP9800Addr=&H4B
  CONST NumberOfUncnfInSensorMode=10
  CONST OnePPSMin=3                             'the number of 1PPS pulses before GPS measurement
  CONST LongSleepTimeMin=1                    'the minimum period of sensor mode is 1 minute
  PIN(GPSPWR)=1: SETPIN GPSPWR,DOUT:PAUSE 100
  PIN(FORCE)=0: SETPIN FORCE,DOUT,OC:PAUSE 100  
  SETPIN BATT,AIN
  PIN(LEDG)=LEDOFF: SETPIN LEDG,DOUT,OC:PAUSE 100
  PIN(LEDR)=LEDOFF: SETPIN LEDR,DOUT,OC:PAUSE 100
  PIN(SELA)=1: SETPIN SELA,DOUT:PAUSE 100
  PIN(SELB)=1: SETPIN SELB,DOUT:PAUSE 100
  PIN(PGD)=1: SETPIN PGD,DOUT:PAUSE 100
  PIN(PGC)=1: SETPIN PGC,DOUT:PAUSE 100
  PIN(LVP)=1: SETPIN LVP,DOUT:PAUSE 100
  PIN(TX1)=1: SETPIN TX1,DOUT:PAUSE 100
  PIN(RNReset)=1: SETPIN RNReset,DOUT:PAUSE 100 ' resets RN2483 module
  PIN(RNReset)=0:PAUSE 100                        ' resets RN2483 module
  PIN(RNReset)=1:PAUSE 100                        ' resets RN2483 module
  SETPIN RNReset,OFF                              ' resets RN2483 module
  SETPIN PUSH,DIN,PULLUP
' variables 
  DIM arg$(20), i, t=0, tGPSfull=0, x$, y$, h$, TIME1$,LatDD, LatMM, LatMMMM, LonDDD, LonMM, LonMMMM, NrSat
  DIM LAT=0,LON=0,ALT=0,DR=0,AllowMotionSensor=0,HDOPinteger
  DIM payload$="",CMD2RN_LoRaWANini$(31),OnePPS=0,ChkSum=0,ChkSumEnd=0
  DIM SensorCounter=0,CO2dat$,CO2limit=65535,CO2ppm=0
  DIM RNReceived=0,NumberOfUncnf=NumberOfUncnfInSensorMode,LEDFlash$="G"
  DIM ButtonPressedByApplicationServer=0      ' pushbutton control from application server
  DIM LongSleepTime=LongSleepTimeMin          ' minutes
  DIM SleepTime=LongSleepTime,PinBat!,BatteryLevelHeader,BatteryLevelPayload
  DIM Mode$="Service"
  DIM GPSpayload$="short"   ' the short GPS payload has only latitude and longitude, the long plus altitude, HDOP, temperature and battery voltage 
  DIM ShortSleepTimeMin=5   ' at long GPSpayload 15sec, at short GPSpayload 5sec
  DIM ShortSleepTime=5      ' seconds 
  DIM GPSMode$="full"       ' or standby during continuous tracking
  DIM MacTxCnf$="uncnf"     ' application indicates if last mac transmission was cfm or uncfm
  DATA "sys reset","mac pause","mac set ch freq 3 867100000","mac set ch freq 4 867300000","mac set ch freq 5 867500000"
  DATA "mac set ch freq 6 867700000","mac set ch freq 7 867900000","mac set ch dcycle 0 9","mac set ch dcycle 1 9"
  Data "mac set ch dcycle 2 9","mac set ch dcycle 3 9","mac set ch dcycle 4 9","mac set ch dcycle 5 9"
  data "mac set ch dcycle 6 9","mac set ch dcycle 7 9","mac set ch drrange 0 0 5","mac set ch drrange 1 0 5"
  data "mac set ch drrange 2 0 5","mac set ch drrange 3 0 5","mac set ch drrange 4 0 5","mac set ch drrange 5 0 5"
  data "mac set ch drrange 6 0 5","mac set ch drrange 7 0 5","mac set ch status 0 on","mac set ch status 1 on"
  data "mac set ch status 2 on","mac set ch status 3 on","mac set ch status 4 on","mac set ch status 5 on"
  data "mac set ch status 6 on","mac set ch status 7 on","mac save"
  for i=0 to 31 : READ CMD2RN_LoRaWANini$(i) : NEXT i  
  I2C OPEN 100,100
  I2C WRITE MCP9800Addr,0,2,1,&B00000001      ' one-shot default mode to CFG register 7bit signed temperature
  I2C CLOSE    
  RN2483OPEN
  PAUSE 200
  PRINT #1,"Usys reset" : PAUSE 50
  WaitsTillRNAnswers
  PAUSE 1000
  x$=INPUT$(200,#1)
  GPSON
' 1sec inturrupt init
  SETTICK 1000,OneSecTick                             ' 1 sec tick time
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ? " "
  ? "  Five second window allows service functions"
  ? " "
  ? "CR/LF to set RN2483"
  ? "C to set LoRaWAN channels"
  ? "R or G to toggle red or green leds"
  ? "T to read temperature"
  ? "V to read battery voltage"
  ? "B to check push button with LEDR"
  ? "3 or 4 to read external CO2 sensors"
  ? "L to check L86 GPS/GNSS receiver"  
FiveSecWait:
  t=0
    TestModes:  
    x$= INKEY$
    SELECT CASE x$                           ' manual service mode for setting RN2483
      CASE chr$(13)
        ? "RN2483 manual setup till ^C"
        RN2483SETUP:
        ONELINE
        PRINT #1,y$
        GOTO RN2483SETUP
      CASE "c","C"                           ' channal configuration of RN2483 modules  
        FOR i=0 to 31
        PRINT #1,CMD2RN_LoRaWANini$(i):PAUSE 50
        ? CMD2RN_LoRaWANini$(i) 'DEBUG
        WaitsTillRNAnswers
        NEXT i
        x$=INKEY$
        t=0
      CASE "R","r"
        ? "R"
        PIN(LEDR)=NOT PIN(LEDR)
        x$=INKEY$
        t=0
      CASE "G","g"
        ? "G"
        PIN(LEDG)=NOT PIN(LEDG)
        x$=INKEY$
        t=0
      CASE "P","p"
        ? "P"
        PIN(LEDR)=LEDOFF
        PULSE LEDR,50
        x$=INKEY$
        t=0
      CASE "T","t"
        ? STR$(ReadsMCP9800Sensor(),3,1)+" C"
        ? HEX$(ReadsMCP9800Sensor(),2)
        x$=INKEY$
        t=0
      CASE "V","v"
        BatteryLevel
        x$=INKEY$
        t=0
      CASE "B","b"                             ' push button test
        ? "push button test"
        PB:
        IF  PIN(PUSH)=0 THEN PIN(LEDR)=LEDON ELSE PIN(LEDR)=LEDOFF
        GOTO PB
      CASE "3"                                ' CO2 sensor on COM3
        RNSleep
        CPU 5
        ? "Reads COZIR on COM3 till ^C"
        PIN(PGC)=0
        PIN(SELA)=0
        PIN(SELB)=1
        SETPIN TX1,OFF
        OPEN "COM1:9600, 100, RxCO2Int3, 3" AS #3
        CO2dat$ = INPUT$(100, #3) 
        DO
        ONELINE
        PRINT #3,y$
        LOOP
      CASE "4"                                ' CO2 sensor on COM4
        RNSleep
        CPU 5
        ? "Reads COZIR on COM4 till ^C"
        PIN(PGD)=0
        PIN(SELA)=1
        PIN(SELB)=1
        SETPIN TX1,OFF
        OPEN "COM1:9600, 100, RxCO2Int4, 3" AS #4
        CO2dat$ = INPUT$(100, #4) 
        DO
        ONELINE
        PRINT #4,y$
        LOOP
      CASE "L","l"                          ' check L86 GPS/GNSS receiver
        ? "Reads GPS sentences till ^C"
        RNSleep
        GPSOPEN
        do
          x$ = input$(1,#2)
          print x$;
        loop        
    END SELECT
    IF t<=5 THEN GOTO TestModes
    ? " "
    ? "The service window is stopped now"
    ? " "
    AllowMotionSensor=1
    PIN(LEDR)=LEDOFF
    PIN(LEDG)=LEDOFF
    ? "temparature =" STR$(ReadsMCP9800Sensor(),3,1)+" C"
    ? "battery voltage:",
    BatteryLevel
    x$=INKEY$
    t=0
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
' RN2483 LoRaWAN init
  Pause 1000                                          ' allows module initialization
  ? "mac resume"
  PRINT #1,"mac resume":PAUSE 50
  WaitsTillRNAnswers
  ? "mac join abp"
  PRINT #1,"mac join abp":PAUSE 50
  WaitsTillRNAnswers
  ? "mac set dr 0"
  PRINT #1,"mac set dr 0":PAUSE 50
  WaitsTillRNAnswers  
  RNSleep
  PAUSE 1000
  Mode$="GPS"
  CO2Measure
  SensorPayloadToLoRaWAN
GPSMode:
  tGPSfull=0 
  CPU 5
  GPSON
  Mode$="GPS"
  SETPIN WAKEUP,INTH,WakeupInt
  SETPIN PPS,INTH,PPSInt,PULLUP
  OnePPS=0
  PAUSE 200
WaitsForPPS:
  IF t<MaxTime THEN GOTO WaitsForPPS2
  GPSOPEN
  GPS2BACKUP
  GPSOFF
  SETPIN WAKEUP,OFF
  ? "CPU sleeps till awaken up by motion sensor or button" 'DEBUG
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  CPU SLEEP  
  ? "CPU awake again" 'DEBUG
  CO2Measure
  SensorPayloadToLoRaWAN
  t=0
  ? t
  GOTO GPSMode
WaitsForPPS2:
  IF PIN(PUSH)=0 THEN GOTO ModeChangeByButton
  IF ButtonPressedByApplicationServer<>0 THEN GOTO ModeChangeByServer
  IF OnePPS<OnePPSMin THEN GOTO WaitsForPPS
  CPU 30                                            ' more MIPS
  GPSOPEN
  SETPIN WAKEUP,OFF
  SETPIN PPS,OFF
  KeepSearching:
  GetGPSRecord                                      ' get a GPS record
  If arg$(0) <> "GPGGA" THEN GOTO KeepSearching
  IF ChkSum <> 0 THEN GOTO KeepSearching
  ? "t=" t 'DEBUG
  IF arg$(6)="0" THEN                               ' invalid
    ? arg$(6)+" search "+arg$(7) 'DEBUG
    GOTO KeepSearching
  ENDIF
    IF arg$(6)="6" THEN
    ? arg$(7)+"sat searching"+arg$(6) 'DEBUG
    GOTO KeepSearching
  ENDIF
  HDOPinteger=VAL(arg$(8))*10
  IF HDOPinteger>250 THEN 
    ? "HDOP>="+HDOPinteger 'DEBUG
    GOTO KeepSearching
  ENDIF
  GPSFull2Standby
  TIME1$ = left$(arg$(1),2) + ":" + MID$(arg$(1),3,2) + ":" + MID$(arg$(1),5,2)  
  LatDD=(val(MID$(arg$(2),1,1))*10+VAL(MID$(arg$(2),2,1)))*600000
  LatMM=(val(MID$(arg$(2),3,1))*10+VAL(MID$(arg$(2),4,1)))*10000
  LatMMMM=(val(MID$(arg$(2),6,1))*1000+VAL(MID$(arg$(2),7,1))*100+val(MID$(arg$(2),8,1))*10+VAL(MID$(arg$(2),9,1)))
  Lat=(LatDD+LatMM+LatMMMM)*8388608\54000000
  IF arg$(3)="S" THEN LAT=-LAT                        ' latitude
  LonDDD=(val(MID$(arg$(4),1,1))*100+VAL(MID$(arg$(4),2,1))*10+VAL(MID$(arg$(4),3,1)))*600000
  LonMM=(val(MID$(arg$(4),4,1))*10+val(MID$(arg$(4),5,1)))*10000
  LonMMMM=(val(MID$(arg$(4),7,1))*1000+VAL(MID$(arg$(4),8,1))*100+val(MID$(arg$(4),9,1))*10+VAL(MID$(arg$(4),10,1)))
  Lon=(LonDDD+LonMM+LonMMMM)*8388608\108000000
  IF arg$(5)="W" THEN Lon=-Lon                        ' longitude
  Alt=VAL(arg$(9))                                    ' Altitude
  If Alt<0 THEN Alt=0
  IF Alt>10000 THEN Alt=10000
  NrSat=VAL(arg$(7))                                  ' number of satellites
  ? arg$(7)+"sat UT"+TIME1$ 'DEBUG
  CPU 10
  RNWakeup
  MacTxCnf$="uncnf"
  payload$="mac tx uncnf 202 "+HEX$(LAT,6)+HEX$(LON,6)
  IF GPSpayload$="long" THEN payload$=payload$+HEX$(ALT,4)+HEX$(HDOPinteger,2)+HEX$(ReadsMCP9800Sensor(),2)+HEX$(BatteryLevelPayload,2)
  ? payload$ 'DEBUG
  LEDFlash$="R"                                       ' 1sec red LED flashing till end of transmission
  PRINT #1,payload$ : PAUSE 50
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  RNSleep
  CPU 5
  IF CO2limit<>65535 THEN CO2Measure
  IF CO2ppm>CO2Limit THEN                             ' 1sec bip on CO2ppm frequency
  ? "bip-bip" 'DEBUG
  SETPIN PGD,OFF
  SETPIN PGC,OFF
  SETPIN LVP,OFF
  PWM 1,CO2ppm,25,100,75
  PAUSE 1000
  pwm 1,STOP
  PIN(PGD)=1: SETPIN PGD,DOUT:PAUSE 1
  PIN(PGC)=1: SETPIN PGC,DOUT:PAUSE 1
  PIN(LVP)=1: SETPIN LVP,DOUT:PAUSE 1
  ENDIF
  ? "CPU sleeps ShortSleepTime =";ShortSleepTime;"sec. Left active time ="; MaxTime-t
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  SETPIN WAKEUP,OFF
  PIN(WAKEUP)=0:SETPIN WAKEUP,DOUT
  CPU Sleep ShortSleepTime
  LEDFlash$="G"
  BatteryLevel 
  SETPIN WAKEUP,OFF 
  SETPIN WAKEUP,INTH,WakeupInt
  ? "CPU awake again" 'DEBUG
  GPSOPEN
  GPSStandby2Full
  SETPIN WAKEUP,INTH,WakeupInt
  SETPIN PPS,INTH,PPSInt,PULLUP
  OnePPS=0
  goto WaitsForPPS
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
ModeChangeByServer:
  IF ButtonPressedByApplicationServer=1 THEN
    CO2Measure
    SensorPayloadToLoRaWAN
    ButtonPressedByApplicationServer=0
    GOTO GPSMode
  ENDIF
  IF ButtonPressedByApplicationServer=2 THEN
    PIN(LEDR)=LEDON
    PAuse 1000
    PIN(LEDR)=LEDOFF
    ButtonPressedByApplicationServer=0
    CO2Measure
    SensorPayloadToLoRaWAN
  GOTO ChangeToSensor    
  ENDIF
  tGPSfull=0
  GOTO GPSMode                          ' neither 1 nor 2
ModeChangeByButton:
  PAUSE 1000
  IF PIN(PUSH)=1 THEN
  PULSE LEDR,500
  CO2Measure
  SensorPayloadToLoRaWAN
  tGPSfull=0
  GOTO GPSMode
  ENDIF
  PIN(LEDR)=LEDON
  MCBB:
  IF PIN(PUSH)=0 THEN GOTO MCBB
  PIN(LEDR)=LEDOFF
  CO2Measure
  SensorPayloadToLoRaWAN
ChangeToSensor:
  ? "change to Sensor mode" 'DEBUG
  NumberOfUncnf=NumberOfUncnfInSensorMode
  Mode$="Sensor"
  PIN(FORCE)=0                        'switch off GPS receiver
  PIN(GPSPWR)=1
  CPU 10
  RNWakeup
  ? "mac set dr 5" 'DEBUG
  PRINT #1,"mac set dr 5":PAUSE 50
  WaitsTillRNAnswers
  ? "mac set adr on" 'DEBUG
  PRINT #1,"mac set adr on":PAUSE 50
  WaitsTillRNAnswers
  ? "mac tx cnf 1 00" 'DEBUG
  PRINT #1,"mac tx cnf 1 00":PAUSE 50
  MacTxCnf$="cnf"
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  ? "mac tx cnf 1 01" 'DEBUG
  PAUSE 5000
  PRINT #1,"mac tx cnf 1 01":PAUSE 50
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  pause 5000
  ? "mac tx cnf 1 02" 'DEBUG
  PRINT #1,"mac tx cnf 1 02":PAUSE 50
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  ? "mac get dr" 'DEBUG
  PRINT #1,"mac get dr":PAUSE 50
  WaitsTillRNAnswers
  IF x$="0" THEN                              ' sets minimum dr to 1 in sensor mode
  ? "mac set dr 1"
  PRINT #1,"mac set dr 1":PAUSE 50
  WaitsTillRNAnswers
  ENDIF
  RNSleep  
  PAUSE 500
  SETPIN WAKEUP,OFF 
  PIN(WAKEUP)=0:SETPIN WAKEUP,DOUT            ' avoids wakeup to float
  PAUSE 100  
SensorMode:  
  i=LongSleepTime
SensorMode1:
  ? "CPU sleeps ";i;" minutes" 'DEBUG
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF 
  CPU SLEEP 58
  PAUSE 500
  BatteryLevel
  IF PIN(PUSH)=0 THEN GOTO ChangeToGPSMode
  If ButtonPressedByApplicationServer=2 THEN GOTO ChangeToGPSMode
  IF i=1 or CO2limit<>65535 THEN CO2Measure
  i=i-1
  IF i=0 THEN
  SensorPayloadToLoRaWAN
  GOTO SensorMode
  ENDIF
  IF CO2ppm>CO2limit THEN SensorPayloadToLoRaWAN
  GOTO SensorMode1
ChangeToGPSMode:
  PIN(LEDG)=LEDON
  PAUSE 1000
  PIN(LEDG)=LEDOFF
  ButtonPressedByApplicationServer=0
  SETPIN WAKEUP,OFF
  PIN(GPSPWR)=0
  PIN(FORCE)=1
    CPU 10
    ? "change to GPS mode" 'DEBUG
    RNWakeup 
    ? "mac set dr 0" 'DEBUG
    PRINT #1,"mac set dr 0":PAUSE 50
    WaitsTillRNAnswers
    ? "mac set adr off" 'DEBUG
    PRINT #1,"mac set adr off":PAUSE 50
    WaitsTillRNAnswers 
    RNSleep
    PAUSE 1000
    SETPIN WAKEUP,INTH,WakeupInt
  PAUSE 100 
  t=0   
GOTO GPSMode
'
' END Main program
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
'             interrupt service routins
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB OneSecTick
  IF LEDFlash$="G" THEN pulse LEDG,5 ELSE PULSE LEDR,5
  t=t+1
  If Mode$="Service" THEN END SUB
  IF Mode$="Sensor" THEN END SUB
  tGPSfull=tGPSfull+1
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RXINT             ' RN2483 RX ISR in background
  Local y$
  RNReceived=1
  x$=""
  ReadRN:
  y$=INPUT$(1,#1)
  IF y$="" THEN GOTO ReadRN
  x$=x$+y$
  if y$<>chr$(10) THEN GOTO ReadRN
  x$=left$(x$,len(x$)-2) 'DEBUG
  ? x$                                                 'DEBUG
  IF LEN(x$)<> 21 THEN END SUB
  IF LEFT$(x$,7)<>"mac_err" THEN GOTO NoMacErr
  IF MacTxCnf$="cnf" THEN GOTO NoMacErr                'mac_err only allowed during cfm type mac transmission
  GOTO CPURestarts                                     'mac_err is not allowed during uncnf mac transmission   
  NoMacErr:
  IF LEFT$(x$,11)<>"mac_rx 209 " THEN END SUB
  IF MID$(x$,12,2)<>"00" THEN ButtonPressedByApplicationServer=VAL(MID$(x$,12,2))        ' push button control from application server
  IF ButtonPressedByApplicationServer<>3 THEN GOTO RXINT1
  IF GPSpayload$="long" THEN GPSpayload$="short" ELSE GPSpayload$="long"
  IF GPSpayload$="long" THEN ShortSleepTimeMin=ShortSleepTimeMin+10 ELSE ShortSleepTimeMin=ShortSleepTimeMin-10
  ButtonPressedByApplicationServer=0
RXINT1:
  ShortSleepTime=VAL("&H"+MID$(x$,14,2))+ShortSleepTimeMin                               ' seconds
  LongSleepTime=VAL("&H"+MID$(x$,16,2))+LongSleepTimeMin                                 ' minutes
  CO2limit=VAL("&H"+MID$(x$,18,4))
  ? "GPSpayload$=";GPSpayload$
  ? "PushButtonPressedByApplicationServer=";ButtonPressedByApplicationServer 'DEBUG
  ? "ShortSleepTime=";ShortSleepTime;" seconds" 'DEBUG
  ? "LongSleepTime=";LongSleepTime;" minutes" 'DEBUG
  ? "CO2limit=";CO2limit;" ppm" 'DEBUG
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''  
SUB WakeupInt                                         ' motion sensor
  IF AllowMotionSensor=0 THEN END SUB
  t=0
  ? "t=";t,"   tGPSfull=",tGPSfull, "  GPS trace mode=",GPSMode$ 'DEBUG
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB PPSInt
  OnePPS=OnePPS+1
  ? "1PPS=";OnePPS 'DEBUG
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
'                                 functions
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
FUNCTION ReadsMCP9800Sensor()                   ' MCP9800 temperature sensor
  LOCAL R
  I2C OPEN 100,100
  I2C WRITE MCP9800Addr,0,2,1,&B10000001       ' start measurement in one-shot mode
  PAUSE 50
  I2C WRITE MCP9800Addr,0,1,0                  ' pointer set to high byte of ambient temperature register  
  I2C READ MCP9800Addr,0,1,R
  I2C CLOSE
  ReadsMCP9800Sensor=R
END FUNCTION
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
'                                 subroutines
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 ' ONELINE Reads one line from consol port
  SUB ONELINE            
  y$=""
  ConsoleTerminal:
  x$=INKEY$
  IF x$="" THEN GOTO ConsoleTerminal
  y$=y$+x$
  if x$<>chr$(13) THEN GOTO ConsoleTerminal
  y$=y$+CHR$(10)
  ? left$(y$,len(y$)-2) 'DEBUG
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
' subroutine to get a GPS sentence into the array arg$()
SUB GetGPSRecord
  DO
    DO WHILE INPUT$(1, #2) <> "$" : LOOP              ' wait for the start
    ChkSum=0
    FOR i = 0 TO 20
      arg$(i) = ""                                    ' clear ready for data
      DO                                              ' loops until a specific exit
        x$ = INPUT$(1, #2)                            ' get the character
        IF x$ <> "*" THEN ChkSum = ChkSum XOR ASC(x$)
        IF x$ = "," THEN EXIT DO                      ' new data item, new field
        IF x$ = "*" THEN
        x$ = INPUT$(1, #2)
        ChkSumEnd=VAL("&H"+x$)*16
        x$ = INPUT$(1, #2)
        ChkSumEnd = ChkSumEnd + VAL("&H"+x$)
        ChkSum = ChkSum XOR ChkSumEnd
        IF ChkSum <> 0 THEN ? "ChkSum=";ChkSum
        EXIT SUB                                      ' end of record, so return with it
        ENDIF
        arg$(i) = arg$(i) + x$                        ' add to the data
      LOOP                                            ' keep going
    NEXT i                                            ' increment the field
  LOOP
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNSleep                                           ' RN2483 to sleep mode
  PRINT #1,"sys sleep 4294967295":PAUSE 50  'RN2483 sleep
  PAUSE 2000
  PIN(SELA)=1
  PIN(SELB)=1
  CLOSE #1
  PIN(TX1)=1 : SETPIN TX1,DOUT
  PAUSE 1
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNWakeup                                          ' wakes up RN2483
  RN2483OPEN
  PAUSE 200
  PRINT #1,"Usys get ver" : PAUSE 50
  WaitsTillRNAnswers
  PAUSE 300
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RN2483OPEN                                        ' OPENS COP port for RN2483
' RN2483 init
  PIN(SELA)=0
  PIN(SELB)=0
  PIN(TX1)=0
  PAUSE 20
  PIN(TX1)=1
  PAUSE 20
  SETPIN TX1,OFF
  OPEN "COM1:57600, 256, RXINT, 3" AS #1  
  x$=INPUT$(200,#1)
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''  
SUB GPSON
  PIN(FORCE)=1
  PIN(GPSPWR)=0 : PAUSE 200
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''  
SUB GPSOFF
  PIN(FORCE)=0 : PAUSE 100 
  PIN(GPSPWR)=1
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''  
' opens GPS COM Port
SUB GPSOPEN
' L86 init
  PIN(SELA)=1
  PIN(SELB)=0
  SETPIN TX1,OFF
  OPEN "COM1:9600" AS #2
  END SUB
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''' 
SUB GPSCLOSE
' closes GPS COM port
  CLOSE #2
  PIN(TX1)=1: SETPIN TX1,DOUT:PAUSE 1
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''    
SUB GPSFull2Standby
  IF tGPSfull<=GPSFullOperationTime THEN
  GPSMode$="full"
  GPSCLOSE
  END SUB
  END IF
  PRINT #2,"$PMTK161,0*28"
  PAUSE 300
  GPSMode$="standby"
  GPSCLOSE
END SUB  
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''    
SUB GPSStandby2Full
  IF GPSMode$="full" THEN
  GPSCLOSE
  END SUB
  END IF
  PRINT #2,"$PMTK161,0*28"
  PAUSE 300
  GPSCLOSE
  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GPS2BACKUP
  PRINT #2,"$PMTK225,4*2F" : PAUSE 300
  GPSCLOSE
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RxCO2Int3
  PAUSE 150
  CO2dat$ = INPUT$(100, #3) 
  CO2dat$ = left$(CO2dat$,LEN(CO2dat$)-2)
  ? SensorCounter;":";DATE$;" ";tiME$;" ";CO2dat$ 'DEBUG
  SensorCounter=SensorCounter+1
END SUB
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''' 
SUB RxCO2Int4
  PAUSE 150
  CO2dat$ = INPUT$(100, #4) 
  CO2dat$ = left$(CO2dat$,LEN(CO2dat$)-2)
  ? SensorCounter;":";DATE$;" ";tiME$;" ";CO2dat$ 'DEBUG
  SensorCounter=SensorCounter+1
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB SensorPayloadToLoRaWAN
  CPU 5
  PIN(TX1)=1 : SETPIN TX1,DOUT  
  PIN(PGC)=1
  PAUSE 1000
  BatteryLevel
  payload$="mac tx "
  IF Mode$="GPS" THEN GOTO AllwaysUNCNF
  IF NumberOfUncnf=0 THEN
  NumberOfUncnf=NumberOfUncnfInSensorMode
  payload$=payload$+"cnf"
  MacTxCnf$="cnf"  
  ELSE
  NumberOfUncnf=NumberOfUncnf-1
AllwaysUNCNF:  
  payload$=payload$+"uncnf"
  MacTxCnf$="uncnf"  
  ENDIF
  payload$=payload$+" 209 "+HEX$(ReadsMCP9800Sensor(),2)+HEX$(BatteryLevelPayload,2)
  IF MID$(CO2dat$,2,1)="Z" THEN payload$=payload$+HEX$(VAL(MID$(CO2dat$,4,5)),4)
  IF MID$(CO2dat$,18,1)="Z" THEN payload$=payload$+HEX$(VAL(MID$(CO2dat$,20,5)),4)
  IF MID$(CO2dat$,2,1)="H" THEN payload$=payload$+HEX$(VAL(MID$(CO2dat$,4,5)),4)
  IF MID$(CO2dat$,10,1)="T" THEN payload$=payload$+RIGHT$(HEX$((VAL(MID$(CO2dat$,12,5))-1000)\10,2),2)
  CPU 10
  RNWakeup
  ? payload$ 'DEBUG
  LEDFlash$="R"
  PRINT #1,payload$:PAUSE 50
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  payload$="mac set bat "+str$(BatteryLevelHeader)
  ? payload$
  PRINT #1,payload$:PAUSE 50
  WaitsTillRNAnswers  
  IF Mode$="GPS" THEN GOTO SFRemains
  ? "mac get dr"
  PRINT #1,"mac get dr":PAUSE 50
  WaitsTillRNAnswers
  IF x$="0" THEN                              ' sets minimum dr to 1 in sensor mode
  ? "mac set dr 1"
  PRINT #1,"mac set dr 1":PAUSE 50
  WaitsTillRNAnswers
  ENDIF  
SFRemains:
  RNSleep
  PAUSE 500
  CPU 5
  LEDFlash$="G"
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB WaitsTillRNAnswers
  LOCAL MaxTime                       ' timeout 30 second maximum (for the sake of "mac tx cnf" command)
  FOR Maxtime= 30000 to 0 STEP -1
  IF RNReceived=1 THEN
  RNReceived=0
  END SUB
  ENDIF
  PAUSE 1
  NEXT MaxTime
CPURestarts:
  PIN(LEDR)=LEDON
  PIN(LEDG)=LEDON
  PAUSE 2000                          ' two seconds red + green light before Micromite restart
  PIN(LEDR)=LEDOFF
  PIN(LEDG)=LEDOFF
  ? "CPU RESTART" 'DEBUG
  CPU RESTART
'  END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB CO2Measure
  PIN(PGC)=0
  PIN(SELA)=0
  PIN(SELB)=1
  SETPIN TX1,OFF
  OPEN "COM1:9600, 100, RxCO2Int3, 3" AS #3
  CO2dat$ = INPUT$(100, #3)
  PAUSE CO2OperatingTime
  PIN(PGC)=1
  PIN(SELA)=1
  PIN(SELB)=1
  CLOSE #3
  CO2ppm=0
  IF MID$(CO2dat$,2,1)="Z" THEN CO2ppm=VAL(MID$(CO2dat$,4,5))
  IF MID$(CO2dat$,18,1)="Z" THEN CO2ppm=VAL(MID$(CO2dat$,20,5))
  ? "CO2ppm=";CO2ppm 'DEBUG
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB BatteryLevel
  PinBat!=PIN(BATT)*2
  IF PinBat!<3.5 THEN PinBat!=3.5
  IF PinBat!>4.2 THEN PinBat!=4.2
  BatteryLevelHeader=INT((PinBat!-3.5)/(4.2-3.5)*253)+1
  BatteryLevelPayload=INT((PinBat!-3.5)/(4.2-3.5)*98)+1
  BatteryLevelPayload=BatteryLevelPayload\10*16+(BatteryLevelPayload/10-BatteryLevelPayload\10)*10
  ? PinBat!,"V BatteryLevelHeader:",
  ? HEX$(BatteryLevelHeader,2)," BatteryLevelPayload:",
  ? HEX$(BatteryLevelPayload,2)
END SUB
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
