  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '           Micromite_GPS_LoRa_Mote_3V63.bas
  ' IF THEN ELSE structure instead of SELECT CASE for service mode selection in order to allow Micromite Lite
  ' C Class and Multicast
  ' Improved UART communication with RN2483
  ' "mac_err" handling after 'mac tx xxx'
  ' Main MMbasic variables stored in flash and allowed to be modified by downlink messaging
  ' improved COZIR power switching
  ' Holman Tamas ChipCAD tholman@chpcad.hu
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  OPTION EXPLICIT
  OPTION AUTORUN ON
  OPTION DEFAULT INTEGER
  CPU 10
    DIM Release=363
  DIM Programmed$
  Programmed$=" "+DATE$+" "+TIME$
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
'  CONST SDA=17                                'digital O or SCL I2C
'  CONST SCL=18                                'digital O or SDA I2C
  CONST TX1=21                                'digital O or TX1
'  CONST RX1=22                                'digital O or RX1
  CONST RNReset=23                            'digital O or RNReset
  CONST PUSH=25                               'digital I
  CONST PPS=26                                'digital I
  CONST LEDON=0,LEDOFF=1
  CONST MCP9800Addr=&H4B
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
  PIN(LVP)=0: SETPIN LVP,DOUT:PAUSE 100
  PIN(TX1)=1: SETPIN TX1,DOUT:PAUSE 100
  PIN(RNReset)=1: SETPIN RNReset,DOUT:PAUSE 100 ' resets RN2483 module
  PIN(RNReset)=0:PAUSE 100                        ' resets RN2483 module
  PIN(RNReset)=1:PAUSE 100                        ' resets RN2483 module
  SETPIN RNReset,OFF                              ' resets RN2483 module
  SETPIN PUSH,DIN,PULLUP
  ' variables
  DIM OnePPSMin=3                           'the number of 1PPS pulses before GPS measurement
  DIM MaxTime=360                           '360 seconds maximum GPS operation time without motion detection
  DIM GPSFullOperationTime=300              '300 seconds in full on mode
  DIM GPSDeviceID=2                         '0 walk, 1 bike, 2 car, 3 boat, 4 airplane, 5 balloon
  DIM FLASH$="EMPTY"                        '
  DIM NRofDR6=1                             ' number of DR=6 transmit insertion into DR=0 transmits in GPS modes
  DIM DR6counter=0
  DIM NumberOfUncnfInSensorMode=12
  DIM Downlink05$=""                        ' during GPS mode the downlink message is processed in main program
  DIM arg$(20),i,t=0,ReceiveTimeout=0,ButtonTimeout=0,MMBREQRNBR,tGPSfull=0,x$,y$,TIME1$,LatDD, LatMM, LatMMMM, LonDDD, LonMM, LonMMMM, NrSat
  DIM LAT=0,LON=0,ALT=0,AllowMotionSensor=0,HDOPinteger,COM1Class=0
  DIM payload$="",CMD2RN_LoRaWANini$(39),OnePPS=0,ChkSum=0,ChkSumEnd=0,CClassMulticast$(5)
  DIM SensorCounter=0,CO2dat$,CO2limit=65535,CO2ppm=0
  DIM RNReceived=0,NumberOfUncnf=NumberOfUncnfInSensorMode,LEDFlash$="G"
  DIM ButtonPressedByApplicationServer=0      ' pushbutton control from application server
  DIM LongSleepTime=LongSleepTimeMin          ' minutes
  DIM PinBat!,BatteryLevelHeader,BatteryLevelPayload
  DIM Mode$="Service"
  DIM GPSpayload$="short"   ' the short GPS payload has only latitude and longitude, the long plus altitude, HDOP, temperature and battery voltage
  DIM ShortSleepTimeMin=5   ' at long GPSpayload 15sec, at short GPSpayload 5sec
  DIM ShortSleepTime=5      ' seconds
  DIM GPSMode$="full"       ' or standby during continuous tracking
  DIM MacTxCnf$="uncnf"     ' application indicates if last mac transmission was cfm or uncfm
  DIM CFilter,MyCFilter,CRed,CGreen,CBlue,dr$,upctr$
  DATA "sys reset","mac pause"
  DATA "mac set ch dcycle 0 9","mac set ch drrange 0 0 5","mac set ch status 0 on"
  DATA "mac set ch dcycle 1 9","mac set ch drrange 1 0 5","mac set ch status 1 on"
  DATA "mac set ch dcycle 2 9","mac set ch drrange 2 0 5","mac set ch status 2 on"
  DATA "mac set ch freq 3 867100000","mac set ch dcycle 3 9","mac set ch drrange 3 0 5","mac set ch status 3 on"
  DATA "mac set ch freq 4 867300000","mac set ch dcycle 4 9","mac set ch drrange 4 0 5","mac set ch status 4 on"
  DATA "mac set ch freq 5 867500000","mac set ch dcycle 5 9","mac set ch drrange 5 0 5","mac set ch status 5 on"
  DATA "mac set ch freq 6 867700000","mac set ch dcycle 6 9","mac set ch drrange 6 0 5","mac set ch status 6 on"
  DATA "mac set ch freq 7 867900000","mac set ch dcycle 7 9","mac set ch drrange 7 0 5","mac set ch status 7 on"
  DATA "mac set ch freq 8 868300000","mac set ch dcycle 8 9","mac set ch drrange 8 6 6","mac set ch status 8 on"
  DATA "mac set ch freq 9 868800000","mac set ch dcycle 9 9","mac set ch drrange 9 7 7","mac set ch status 9 on"
  DATA "mac save"
  for i=0 to 39 : READ CMD2RN_LoRaWANini$(i): NEXT i
  DATA "mac set deveui CCCCCCCCCCCCCCCC","mac set devaddr 01DA5110"
  DATA "mac set nwkskey 46126EEEDEAEBCC471EE8FEA7500DB66","mac set appskey 37E5A3A61C9FFE14122F20DAFD232377"
  DATA "mac set dr 0","mac join abp"
  for i=0 to 5 : READ CClassMulticast$(i): NEXT i
  VAR RESTORE                               ' without flash initialization this doesn't modify RAM varables
  IF FLASH$="EMPTY" THEN                    ' initializes variables in flash memory, this runs only once
    FLASH$="NO"
    VAR SAVE GPSDeviceID,OnePPSMin,GPSFullOperationTime,MaxTime,NumberOfUncnfInSensorMode,NRofDR6
    VAR SAVE FLASH$,GPSpayload$,ShortSleepTime,LongSleepTime,CO2limit,Programmed$
  END IF
  ? "Micromite GPS LoRa Mote ";fix(Release/100);"v"+STR$(Release-100*fix(Release/100),1)+Programmed$
  I2C OPEN 100,100
  I2C WRITE MCP9800Addr,0,2,1,&B00000001      ' one-shot default mode to CFG register 7bit signed temperature
  I2C CLOSE
  RN2483OPEN
  PAUSE 200
  PRINT #1,"Usys reset" : COM1TXEmpty
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
  ? "c to set LoRaWAN channels"
  ? "r or g to toggle red or green leds"
  ? "t to read temperature"
  ? "v to read battery voltage"
  ? "b to check push button with LEDR"
  ? "3 or 4 to read external CO2 sensors"
  ? "l to check L86 GPS/GNSS receiver"
FiveSecWait:
  t=0
ServiceModes:
  x$= INKEY$
  IF x$<> chr$(13) THEN GOTO ChannelConfig
  ? "RN2483 manual setup till ^C"
RN2483SETUP:
  ONELINE
  PRINT #1,y$
  GOTO RN2483SETUP
ChannelConfig:
  IF x$<>"c" THEN GOTO ToggleRLED           ' channal configuration of RN2483 modules
  for i=0 TO 39
    PRINT #1,CMD2RN_LoRaWANini$(i):COM1TXEmpty
    ? CMD2RN_LoRaWANini$(i)                 'DEBUG
    WaitsTillRNAnswers
  NEXT i
  x$=INKEY$
  t=0
ToggleRLED:
  IF x$<>"r" THEN GOTO ToggleGLED
  ? "r"
  PIN(LEDR)=NOT PIN(LEDR)
  x$=INKEY$
  t=0
ToggleGLED:
  IF x$<>"g" THEN GOTO PulseR
  ? "g"
  PIN(LEDG)=NOT PIN(LEDG)
  x$=INKEY$
  t=0
PulseR:
  IF x$<>"p" THEN GOTO TempSensor
  PIN(LEDR)=LEDOFF
  PULSE LEDR,50
  x$=INKEY$
  t=0
TempSensor:
  IF x$<>"t" THEN GOTO VoltageSensor
  ? STR$(ReadsMCP9800Sensor(),3,1)+" C"
  ? HEX$(ReadsMCP9800Sensor(),2)
  x$=INKEY$
  t=0
VoltageSensor:
  IF x$<> "v" THEN GOTO ButtonTest
  BatteryLevel
  x$=INKEY$
  t=0
ButtonTest:
  IF x$<>"b" THEN GOTO COM3
  ? "push button test"
PB:
  IF  PIN(PUSH)=0 THEN PIN(LEDR)=LEDON ELSE PIN(LEDR)=LEDOFF
  GOTO PB
COM3:
  IF x$<>"3" THEN GOTO COM4                      ' CO2 sensor on COM3
  RNSleep
  CPU 5
  ? "Reads COZIR on COM3 till ^C"
  PIN(PGC)=0
  PIN(SELA)=0
  PIN(SELB)=1
  SETPIN TX1,OFF
  OPEN "COM1:9600, 100, RxCO2Int3, 1" AS #3
  CO2dat$ = INPUT$(100, #3)
  DO
    ONELINE
    PRINT #3,y$
  LOOP
COM4:
  IF x$<>"4" THEN GOTO GPSGNSTEST              ' CO2 sensor on COM4
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
GPSGNSTEST:
  IF x$<>"l" THEN GOTO ENDservice
  ? "Reads GPS sentences till ^C"
  RNSleep
  GPSOPEN
  do
    x$ = input$(1,#2)
    print x$;
  loop
ENDservice:
  IF t<=5 THEN GOTO ServiceModes
  ? " "
  ? "The service window is stopped now"
  ? " "
  PIN(PGC)=1                                  ' stops CO2 sensor power
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
  PRINT #1,"mac resume":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac join abp"
  PRINT #1,"mac join abp":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set dr 0"
  PRINT #1,"mac set dr 0":COM1TXEmpty
  WaitsTillRNAnswers
  RNSleep
  PAUSE 1000
  Mode$="GPS"
  CO2Measure
  SensorPayloadToLoRaWAN
  VariablesToLoRaWAN
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
  PAUSE 5000                                        ' allows motion sensor - wakeup pin to set
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  CPU SLEEP
  ? "CPU awake again" 'DEBUG
  CO2Measure
  SensorPayloadToLoRaWAN  
  VariablesToLoRaWAN
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
  ? "Micromite reads valid GPS data"
KeepSearching:
  GetGPSRecord                                      ' get a GPS record
  If arg$(0) <> "GPGGA" THEN GOTO KeepSearching
  IF ChkSum <> 0 THEN GOTO KeepSearching
  ? "t=" t 'DEBUG
  IF arg$(6)="0" THEN                               ' invalid
    ? arg$(6)+" search "+arg$(7) 'DEBUG
    GPSCLOSE
    GOTO GPSMode
  ENDIF
  IF arg$(6)="6" THEN
    ? arg$(7)+"sat searching"+arg$(6) 'DEBUG
    GOTO KeepSearching
  ENDIF
  HDOPinteger=VAL(arg$(8))*10
  IF HDOPinteger>250 THEN
    ? "HDOP>=";HDOPinteger 'DEBUG
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
  WaitsTillRNAnswers
  MacTxCnf$="uncnf"
  payload$="mac tx uncnf 202 "+HEX$(LAT,6)+HEX$(LON,6)+HEX$(ALT,4)
  IF GPSpayload$="long" THEN payload$=payload$+HEX$(HDOPinteger,2)+HEX$(ReadsMCP9800Sensor(),2)+HEX$(BatteryLevelPayload,2)
  IF NRofDR6=0 THEN GOTO SendGPSPayload
  IF DR6counter<>0 THEN
    DR6counter=DR6counter-1
    ? "mac set dr 6"
    PRINT #1,"mac set dr 6":COM1TXEmpty
    WaitsTillRNAnswers
    GOTO SendGPSPayload
  END IF
  DR6counter=NRofDR6
  ? "mac set dr 0"
  PRINT #1,"mac set dr 0":COM1TXEmpty
  WaitsTillRNAnswers
SendGPSPayload:
  IF Downlink05$="" THEN GOTO SendGPSPayload2
  x$=Downlink05$
  Downlink05$=""
  GPSDeviceID=VAL("&H"+MID$(x$,14,1))
  OnePPSMin=VAL("&H"+MID$(x$,15,1))
  IF VAL("&H"+MID$(x$,16,2))=0 THEN MaxTime=60 ELSE MaxTime=60*VAL("&H"+MID$(x$,16,2))
  IF VAL("&H"+MID$(x$,18,2))=0 THEN GPSFullOperationTime=60 ELSE GPSFullOperationTime=60*VAL("&H"+MID$(x$,18,2))
  NRofDR6=VAL("&H"+MID$(x$,20,1))
  IF VAL("&H"+MID$(x$,21,1))=0 THEN NumberOfUncnfInSensorMode=4 ELSE NumberOfUncnfInSensorMode=4*VAL("&H"+MID$(x$,21,1))
  VAR SAVE GPSDeviceID,OnePPSMin,MaxTime,GPSFullOperationTime,NRofDR6,NumberOfUncnfInSensorMode
  ? MID$(x$,12,10)
  ? "GPSDeviceID=";GPSDeviceID
  ? "OnePPSMin=";OnePPSMin
  ? "MaxTime=";MaxTime
  ? "GPSFullOperationTime=";GPSFullOperationTime
  ? "NRofDR6=";NRofDR6
  ? "NumberOfUncnfInSensorMode=";NumberOfUncnfInSensorMode
  IF NRofDR6=0 THEN
    ? "mac set dr 0"
    PRINT #1,"mac set dr 0":COM1TXEmpty
    WaitsTillRNAnswers
  END IF
  DR6counter=NRofDR6
SendGPSPayload2:
  ? payload$ 'DEBUG
  LEDFlash$="R"                                       ' 1sec red LED flashing till end of transmission
  PRINT #1,payload$ : COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MacError
  payload$="mac set bat "+str$(BatteryLevelHeader)
  ? payload$
  PRINT #1,payload$:COM1TXEmpty
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
    PIN(LVP)=0: SETPIN LVP,DOUT:PAUSE 1
  ENDIF
  ? "CPU sleeps ShortSleepTime =";ShortSleepTime;"sec. Left active time ="; MaxTime-t
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  SETPIN PPS,OFF
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
  IF ButtonPressedByApplicationServer=4 THEN
    ButtonPressedByApplicationServer=0
    PIN(FORCE)=0                        'switch off GPS receiver
    PIN(GPSPWR)=1
    CPU 10
    GOTO Multicast
  ENDIF
  IF ButtonPressedByApplicationServer=1 THEN
    CO2Measure
    SensorPayloadToLoRaWAN
    VariablesToLoRaWAN
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
  GOTO GPSMode                                              ' neither 1 nor 2
ModeChangeByButton:
  ButtonTimeout=0
MCBB:
  IF ButtonTimeout>=2 THEN  PIN(LEDR)=LEDON
  IF ButtonTimeout>=4 THEN PIN(LEDG)=LEDON
  IF PIN(PUSH)=0 THEN GOTO MCBB
  IF ButtonTimeout<2 THEN
    PULSE LEDR,100
    CO2Measure
    SensorPayloadToLoRaWAN
    VariablesToLoRaWAN
    tGPSfull=0
    GOTO GPSMode
  ENDIF
  IF ButtonTimeout<4 THEN
    PIN(LEDR)=LEDOFF
    CO2Measure
    SensorPayloadToLoRaWAN
    GOTO ChangeToSensor
  ENDIF
  IF ButtonTimeout>=4 THEN
    PIN(FORCE)=0                        'switch off GPS receiver
    PIN(GPSPWR)=1
    CPU 10
    PIN(LEDR)=LEDOFF
    PIN(LEDG)=LEDOFF
    CFilter=22
    CRed=0
    CGreen=0
    CBlue=0
    GOTO Multicast
  eNDIF
  GOTO MCBB
ChangeToSensor:
  ? "change to Sensor mode" 'DEBUG
  NumberOfUncnf=NumberOfUncnfInSensorMode
  Mode$="Sensor"
  PIN(FORCE)=0                        'switch off GPS receiver
  PIN(GPSPWR)=1
  CPU 10
  RNWakeup
  WaitsTillRNAnswers
  ? "mac set dr 5" 'DEBUG
  PRINT #1,"mac set dr 5":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set adr on" 'DEBUG
  PRINT #1,"mac set adr on":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac tx cnf 1 00" 'DEBUG
  PRINT #1,"mac tx cnf 1 00":COM1TXEmpty
  MacTxCnf$="cnf"
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MacError
  PAUSE 10000
  ? "mac tx cnf 1 01" 'DEBUG
  PRINT #1,"mac tx cnf 1 01":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MacError
  ? "mac get dr" 'DEBUG
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  IF x$="0" THEN                              ' sets minimum dr to 1 in sensor mode
    ? "mac set dr 1"
    PRINT #1,"mac set dr 1":COM1TXEmpty
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
  IF PIN(PUSH)=0 THEN GOTO ChangeToGPSMode
  If ButtonPressedByApplicationServer=2 THEN GOTO ChangeToGPSMode
  If ButtonPressedByApplicationServer=4 THEN GOTO Multicast
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
  DO WHILE PIN(PUSH)=0
  LOOP
  PIN(LEDG)=LEDOFF
  ButtonPressedByApplicationServer=0
  SETPIN WAKEUP,OFF
  PIN(GPSPWR)=0
  PIN(FORCE)=1
  CPU 10
  ? "change to GPS mode" 'DEBUG
  RNWakeup
  WaitsTillRNAnswers
  ? "mac set dr 0" 'DEBUG
  PRINT #1,"mac set dr 0":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set adr off" 'DEBUG
  PRINT #1,"mac set adr off":COM1TXEmpty
  WaitsTillRNAnswers
  RNSleep
  PAUSE 1000
  SETPIN WAKEUP,INTH,WakeupInt
  PAUSE 100
  t=0
  GOTO GPSMode
Multicast:                                   ' controlling RGB LED by C Class RGB messages
  AllowMotionSensor=0
  COM1Class=1
  RNWakeup
  RNRXPoll
  RNRXPoll
  ? "mac set adr off"
  PRINT #1,"mac set adr off":COM1TXEmpty
  RNRXPoll
  ? "mac tx cnf 222 ff" 'DEBUG
  PRINT #1,"mac tx cnf 222 ff":COM1TXEmpty
  RNRXPoll
  RNRXPoll
  MyCFilter=CFilter
  ? "MyCFilter=",MyCFilter
  FOR I=0 TO 5
    ? CClassMulticast$(i) 'DEBUG
    PRINT #1,CClassMulticast$(i):COM1TXEmpty
    RNRXPoll
  NEXT i
  RNRXPoll
  IF x$<>"accepted" THEN RNRXPOLL
  ? "mac tx cnf 222 ff" 'DEBUG
  PRINT #1,"mac tx cnf 222 ff":COM1TXEmpty
  RNRXPoll
  RNRXPoll
  MMBREQRNBR=-3600                                             ' syncronize baudrates at every 10 minutes
OpensRX2:
  ? ""
  IF MMBREQRNBR>-200 THEN ? "MMBREQRNBR=",MMBREQRNBR
  IF MMBREQRNBR>0 THEN Syncronise
  ? "radio rx 450" 'DEBUG
  IF PIN(PUSH)=0 THEN CPU RESTART                             ' goes bck to GPS by button press
  PRINT #1,"radio rx 450":COM1TXEmpty
  RNRXPoll
  RNRXPoll
  IF LEFT$(x$,7)="mac_err" THEN GOTO OpensRX2
  IF LEFT$(x$,9)="mac_tx_ok" THEN GOTO OpensRX2
  IF LEFT$(x$,7)="timeout" THEN
    RN2483SoftwareReset
    GOTO OpensRX2
  END IF
  IF CFilter=0 THEN CPU RESTART                               ' goes back to GPS by server 0 filter
  IF CFilter=MyCFilter THEN PWM 1,200,100-CRed,100-CBlue,100-CGreen
  GOTO OpensRX2
SUB Syncronise
  ? "Syncronize baudrates"
  ? "sys sleep 4294967295"
  PRINT #1,"sys sleep 4294967295":COM1TXEmpty
  PAUSE 500
  CLOSE #1
  PIN(TX1)=1 : SETPIN TX1,DOUT
  PAUSE 1
  PIN(TX1)=0 : SETPIN TX1,DOUT
  PAUSE 1
  PIN(TX1)=1 : SETPIN TX1,DOUT
  PAUSE 1
  SETPIN TX1,OFF
  OPEN "COM1:57600" AS #1
  PRINT #1,"Usys get ver" : COM1TXEmpty
  RNRXPoll
  RNRXPOLL
  MMBREQRNBR=-3600
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '             interrupt service routins
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB OneSecTick
  IF LEDFlash$="G" THEN pulse LEDG,5 ELSE PULSE LEDR,5
  t=t+1
  ReceiveTimeout=ReceiveTimeout+1
  ButtonTimeout=ButtonTimeout+1
  MMBREQRNBR=MMBREQRNBR+1                                   'RN2483 baudrate = Micromite baudrate once in every 10 minutes
  If Mode$="Service" THEN END SUB
  IF Mode$="Sensor" THEN END SUB
  tGPSfull=tGPSfull+1
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RXINT             ' RN2483 RX ISR in background
  RNReceived=1
  Local y$
  x$=""
ReadRN:
  y$=INPUT$(1,#1)
  IF y$="" THEN GOTO ReadRN
  x$=x$+y$
  if y$<>chr$(10) THEN GOTO ReadRN
  x$=left$(x$,len(x$)-2) 'DEBUG
  ? x$                                                 'DEBUG
  IF LEN(x$)<> 21 THEN END SUB
  IF LEFT$(x$,11)<>"mac_rx 209 " THEN END SUB
  IF VAL(MID$(x$,12,2))=>6 THEN
    ? MID$(x$,12,2)," is not a valid downlink command"
END SUB                                                                                ' returns if not valid downlink message arrived
  ENDIF
  ButtonPressedByApplicationServer=VAL(MID$(x$,12,2))                                    ' push button control from application server
  IF ButtonPressedByApplicationServer=5 THEN GOTO RXINT5
  IF ButtonPressedByApplicationServer=4 THEN GOTO RXINT4
  IF ButtonPressedByApplicationServer<>3 THEN GOTO RXINT1
  IF GPSpayload$="long" THEN GPSpayload$="short" ELSE GPSpayload$="long"
  IF GPSpayload$="long" THEN ShortSleepTimeMin=ShortSleepTimeMin+10 ELSE ShortSleepTimeMin=ShortSleepTimeMin-10
  ButtonPressedByApplicationServer=0
RXINT1:
  ShortSleepTime=VAL("&H"+MID$(x$,14,2))+ShortSleepTimeMin                               ' seconds
  LongSleepTime=VAL("&H"+MID$(x$,16,2))+LongSleepTimeMin                                 ' minutes
  CO2limit=VAL("&H"+MID$(x$,18,4))
  ? "ButtonPressedByApplicationServer=",ButtonPressedByApplicationServer
  ? "GPSpayload$=";GPSpayload$
  ? "ShortSleepTime=";ShortSleepTime;" seconds" 'DEBUG
  ? "LongSleepTime=";LongSleepTime;" minutes" 'DEBUG
  ? "CO2limit=";CO2limit;" ppm" 'DEBUG
  VAR SAVE ShortSleepTime,LongSleepTime,CO2limit,GPSpayload$
END SUB
RXINT4:
  CFilter=VAL(MID$(x$,14,2))
  ? "CFilter=",CFilter
  CRed=VAL(MID$(x$,16,2))
  ? "CRed=",CRed
  CGreen=VAL(MID$(x$,18,2))
  ? "CGreen=",CGreen
  CBlue=VAL(MID$(x$,20,2))
  ? "CBlue=",CBlue
END SUB
RXINT5:
  ButtonPressedByApplicationServer=0
  IF Mode$="GPS" THEN
    Downlink05$=x$
END SUB
  END IF
  GPSDeviceID=VAL("&H"+MID$(x$,14,1))
  OnePPSMin=VAL("&H"+MID$(x$,15,1))
  IF VAL("&H"+MID$(x$,16,2))=0 THEN MaxTime=60 ELSE MaxTime=60*VAL("&H"+MID$(x$,16,2))
  IF VAL("&H"+MID$(x$,18,2))=0 THEN GPSFullOperationTime=60 ELSE GPSFullOperationTime=60*VAL("&H"+MID$(x$,18,2))
  NRofDR6=VAL("&H"+MID$(x$,20,1))
  IF VAL("&H"+MID$(x$,21,1))=0 THEN NumberOfUncnfInSensorMode=4 ELSE NumberOfUncnfInSensorMode=4*VAL("&H"+MID$(x$,21,1))
  VAR SAVE GPSDeviceID,OnePPSMin,MaxTime,GPSFullOperationTime,NRofDR6,NumberOfUncnfInSensorMode
  ? MID$(x$,12,10)
  ? "GPSDeviceID=";GPSDeviceID
  ? "OnePPSMin=";OnePPSMin
  ? "MaxTime=";MaxTime
  ? "GPSFullOperationTime=";GPSFullOperationTime
  ? "NRofDR6=";NRofDR6
  ? "NumberOfUncnfInSensorMode=";NumberOfUncnfInSensorMode
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
SUB RxCO2Int3
  PAUSE 100
  CO2dat$ = INPUT$(100, #3)
  CO2dat$ = left$(CO2dat$,LEN(CO2dat$)-2)
  ? SensorCounter;":";DATE$;" ";tiME$;" ";CO2dat$ 'DEBUG
  SensorCounter=SensorCounter+1
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RxCO2Int4
  PAUSE 100
  CO2dat$ = INPUT$(100, #4)
  CO2dat$ = left$(CO2dat$,LEN(CO2dat$)-2)
  ? SensorCounter;":";DATE$;" ";tiME$;" ";CO2dat$ 'DEBUG
  SensorCounter=SensorCounter+1
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
  IF LEN(y$)=2 THEN ? y$ ELSE ? left$(y$,len(y$)-2) 'DEBUG
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
SUB RNSleep                                               ' RN2483 to sleep mode
  PRINT #1,"sys sleep 4294967295":COM1TXEmpty  'RN2483 sleep
  PAUSE 2000
  PIN(SELA)=1
  PIN(SELB)=1
  CLOSE #1
  PIN(TX1)=1 : SETPIN TX1,DOUT
  PAUSE 1
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNWakeup                                              ' wakes up RN2483
  RN2483OPEN
  PRINT #1,"Usys get ver" : COM1TXEmpty
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
  IF COM1Class=0 THEN OPEN "COM1:57600, 256, RXINT, 3" AS #1 ELSE OPEN "COM1:57600" AS #1
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
  PAUSE 300
  PIN(SELA)=1
  PIN(SELB)=1
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
  PRINT #2,"$PMTK161,0*28":COM2TXEmpty
  GPSMode$="standby"
  GPSCLOSE
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GPSStandby2Full
  IF GPSMode$="full" THEN
    GPSCLOSE
END SUB
  END IF
  PRINT #2," ":COM2TXEmpty
  GPSCLOSE
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GPS2BACKUP
  PRINT #2,"$PMTK225,4*2F":COM2TXEmpty
  GPSCLOSE
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  
SUB SensorPayloadToLoRaWAN
  CPU 5
  PIN(TX1)=1 : SETPIN TX1,DOUT
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
  WaitsTillRNAnswers
  ? payload$ 'DEBUG
  LEDFlash$="R"
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MacError
  payload$="mac set bat "+str$(BatteryLevelHeader)
  ? payload$
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  IF Mode$="GPS" THEN GOTO SFRemains
  ? "mac get dr"
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  IF x$="0" THEN                              ' sets minimum dr to 1 in sensor mode
    ? "mac set dr 1"
    PRINT #1,"mac set dr 1":COM1TXEmpty
    WaitsTillRNAnswers
  ENDIF
SFRemains:
  RNSleep
  PAUSE 500
  CPU 5
  LEDFlash$="G"
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB CO2Measure
  PIN(PGC)=0
  PAUSE 500
  ReceiveTimeout=0
  PIN(SELA)=0
  PIN(SELB)=1
  SETPIN TX1,OFF
  OPEN "COM1:9600" AS #3
  CO2dat$=INPUT$(255,#3)
  CO2dat$=""
CO2Mloop:
  IF ReceiveTimeout=3 THEN GOTO CloseCO2Measurement
  y$=INPUT$(1,#3)
  IF y$="" THEN GOTO CO2Mloop
  CO2dat$=CO2dat$+y$
  if y$<>chr$(10) THEN GOTO CO2Mloop
  CO2dat$=left$(CO2dat$,len(CO2dat$)-2) 'DEBUG
  ? CO2dat$
CloseCO2Measurement:
  PIN(PGC)=1
  CLOSE #3
  PIN(SELA)=1
  PIN(SELB)=1
  PIN(TX1)=1: SETPIN TX1,DOUT:PAUSE 1
  CO2ppm=0
  IF INSTR(1,CO2dat$,"z")<>0 THEN CO2ppm=VAL(MID$(CO2dat$,INSTR(1,CO2dat$,"z")+3,5))
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
  ? STR$(BatteryLevelHeader,2)," BatteryLevelPayload:",
  ? HEX$(BatteryLevelPayload,2)
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB COM1TXEmpty
  DO WHILE LOF(#1)<>256
  LOOP
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB COM2TXEmpty
  DO WHILE LOF(#2)<>256
  LOOP
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB WaitsTillRNAnswers
  ReceiveTimeout=0                        ' 200 seconds timeout on RX RN2483
WaitsTillRNAnswers0:
  IF ReceiveTimeout=200 then
    PIN(LEDR)=LEDON
    PIN(LEDG)=LEDON
    PAUSE 2000                          ' two seconds red + green light before Micromite restarts
    PIN(LEDR)=LEDOFF
    PIN(LEDG)=LEDOFF
    ? "CPU RESTART" 'DEBUG
    CPU RESTART
  ENDIF
  IF RNReceived=0 THEN GOTO WaitsTillRNAnswers0   'waits for the first character into receive buffer
  RNReceived=0
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNRXPoll
  ReceiveTimeout=0
  Local y$=""
  x$=""
  '    ? "v:"
RNPoll:
  y$=INPUT$(1,#1)
  IF ReceiveTimeout=17 then
    PIN(LEDR)=LEDON
    PIN(LEDG)=LEDON
    PAUSE 100                          ' 100ms red + green light before Micromite restarts
    PIN(LEDR)=LEDOFF
    PIN(LEDG)=LEDOFF
    '        ? "CPU RESTART" 'DEBUG
    '        CPU RESTART
    ? "timeout"
    x$="timeout"
END SUB
  ENDIF
  IF y$="" THEN GOTO RNPoll
  '    ? hex$(asc(y$),2);
  x$=x$+y$
  if y$<>chr$(10) THEN GOTO RNPoll
  '    ? " itt a rekord vege"
  x$=left$(x$,len(x$)-2) 'DEBUG
  ? x$                                                 'DEBUG
  IF LEN(x$)<> 21 THEN END SUB
  IF LEFT$(x$,11)<>"mac_rx 209 " THEN END SUB
  IF VAL(MID$(x$,12,2))<>4 THEN
    ? MID$(x$,12,2)," is not a valid C-Class command"
END SUB                                                                                ' returns if not valid downlink message arrived
  ENDIF
  CFilter=VAL(MID$(x$,14,2))
  ? "CFilter=",CFilter,"   ";
  CRed=VAL(MID$(x$,16,2))
  ? "CRed=",CRed,"   ";
  CGreen=VAL(MID$(x$,18,2))
  ? "CGreen=",CGreen,"   ";
  CBlue=VAL(MID$(x$,20,2))
  ? "CBlue=",CBlue,"   "
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB MacError
  IF LEFT$(x$,7)<>"mac_err" THEN END SUB
  ? "mac get dr"
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  dr$=x$
  ? "mac get upctr"
  PRINT #1,"mac get upctr":COM1TXEmpty
  WaitsTillRNAnswers
  upctr$=x$
  CLOSE #1
  PIN(TX1)=1 : SETPIN TX1,DOUT : PAUSE 10
  PIN(TX1)=0 : PAUSE 10
  PIN(TX1)=1 : PAUSE 1
  SETPIN TX1,OFF
  OPEN "COM1:57600, 256, RXINT, 3" AS #1
  PRINT #1,"Usys reset" : COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac join abp"
  PRINT #1,"mac join abp":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set dr "+dr$
  PRINT #1,"mac set dr "+dr$:COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set upctr "+upctr$
  PRINT #1,"mac set upctr "+upctr$:COM1TXEmpty
  WaitsTillRNAnswers
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB VariablesToLoRaWAN
  payload$="mac tx uncnf 203 "+HEX$(GPSDeviceID,1)+HEX$(OnePPSMin,1)+HEX$(MaxTime/60,2)+HEX$(GPSFullOperationTime/60,2)
  payload$=payload$+HEX$(NRofDR6,1)+HEX$(NumberOfUncnfInSensorMode/4,1)+HEX$(ShortSleepTime-5,2)+HEX$(LongSleepTime-1,2)
  payload$=payload$+HEX$(CO2limit,4)
  IF Release<1000 THEN payload$=payload$+"0"+STR$(Release) ELSE payload$=payload$+STR$(Release)
  PAUSE 5000
  CPU 10
  RNWakeup
  WaitsTillRNAnswers
  ? payload$ 'DEBUG
  LEDFlash$="R"
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MacError
  RNSleep
  PAUSE 500
  CPU 5
  LEDFlash$="G"
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RN2483SoftwareReset                         ' While RN2483 UART is polled in C Class
  ? "sys reset" 'DEBUG
  PRINT #1,"sys reset":COM1TXEmpty
  PAUSE 1000
  RNRXPoll
  FOR I=0 TO 5
    ? CClassMulticast$(i) 'DEBUG
    PRINT #1,CClassMulticast$(i):COM1TXEmpty
    RNRXPoll
  NEXT i
  RNRXPoll
  IF x$<>"accepted" THEN RNRXPOLL
  ? "mac tx cnf 222 ff" 'DEBUG
  PRINT #1,"mac tx cnf 222 ff":COM1TXEmpty
  RNRXPoll
  RNRXPoll
END SUB
