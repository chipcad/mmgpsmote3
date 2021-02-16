  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '                            Micromite_GPS_LoRa_Mote_5v12.bas
  '           2020 November 05. Turn off DutyCycleReq Duty Cycle Request after join otaa. Duty Cycle control remains at Micromite Application level.
  '           Change "sys sleep 4294967295" command to "4294967296" on December 15 2019
  '           Adding range tester to Service functions for EMBIT LoRaEMB network on August 20 2019
  '           RSSI and SNR to GPS2Sensor payload and Multicast echo on May 19 2019, default GPS format is Adeunis Lagacy
  '           Appeui setting in service mode allows secure movement of devices to other account
  '           The default activation is OTAA
  '           OTAA requires appeu and appkey, customers are encouraged to create these keys in their network server
  '                                       (c) Holman Tamas ChipCAD tholman@chipcad.hu
  ' Main:         Initialization
  '               Service_mode
  '               GPS_mode
  '               Sensor_mode
  '               Multicast_mode
  ' Interrupts:   OneSecTick
  '               WakeupInt
  '               PPSInt
  '               RxCO2Int3
  '               RxCO2Int4
  ' Functions:    ReadsMCP9800Sensor()
  '               ONELINE$()
  '               H2B$(Hexa$)                'EMBIT service
  '               B2H$(Binary$)              'EMBIT service
  ' Subroutines:  GetGPSRecord
  '               RNSleep
  '               RNWakeup
  '               RN2483OPEN
  '               GPSON
  '               GPSOFF
  '               GPSOPEN
  '               GPSCLOSE
  '               GPSFull2Standby
  '               GPSStandby2Full
  '               GPS2BACKUP
  '               SensorPayloadToLoRaWAN
  '               CO2Measure
  '               BatteryLevel
  '               COM1TXEmpty
  '               COM2TXEmpty
  '               WaitsTillRNAnswers
  '               RNRestart
  '               PT                        Path Through conslole to RN Module
  '               VariablesToLoRaWAN
  '               SM1131_TH06
  '               GetRSSIandSNR
  '               X2RSSISNR
  '               COM1toCOM3                'EMBIT service
  '               COM3toCOM1                'EMBIT service
  '               EMBITTCVR(Hexa$)          'EMBIT service
  '               TurnOffChannelsDutyCyleControl
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' Initialization:
  OPTION EXPLICIT
  OPTION AUTORUN ON
  OPTION DEFAULT INTEGER
  CPU 10
  DIM Release=512
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
  PIN(GPSPWR)=1: SETPIN GPSPWR,DOUT
  PIN(FORCE)=0: SETPIN FORCE,DOUT,OC
  SETPIN BATT,AIN
  PIN(LEDG)=LEDOFF: SETPIN LEDG,DOUT,OC
  PIN(LEDR)=LEDOFF: SETPIN LEDR,DOUT,OC
  PIN(SELA)=1: SETPIN SELA,DOUT
  PIN(SELB)=1: SETPIN SELB,DOUT
  PIN(PGD)=1: SETPIN PGD,DOUT
  PIN(PGC)=1: SETPIN PGC,DOUT
  PIN(LVP)=1: SETPIN LVP,DOUT
  '  PIN(TX1)=1: SETPIN TX1,DOUT
  SETPIN PUSH,DIN,PULLUP
  ' variables
  DIM OnePPSMin=3                           'the number of 1PPS   pulses before GPS measurement
  DIM MaxTime=360                           '360 seconds maximum GPS operation time without motion detection
  DIM GPSFullOperationTime=300              '300 seconds in full on mode
  DIM GPSDeviceID=3                         '0 walk, 1 bicycle, 2 bike, 3 vehicle, 4 train, 5 boat, 6 drone, 7 balloon, 8 airplane, 9 animal
  DIM GPSFormat=4                           '0 Micromite Short, 1 Micromite Long, 2 Semtech, 3 Adeunis, 4 Adeunis Lagacy
  DIM SM1131correction=0                    ' corrects measured pressure of SM1131
  DIM QNH=1013                              ' actual pressure on see level
  DIM ReferenceHeight=0                     ' known above see level height of SM1131 calibration
  DIM FLASH$="EMPTY"                        '
  DIM NRofDR6=1                             ' number of DR=6 transmit insertion into DR=0 transmits in GPS modes
  DIM DR6counter=0
  DIM NumberOfUncnfInSensorMode=12
  DIM Downlink05$=""                        ' during GPS mode the downlink message is processed in main program
  DIM arg$(20),i,f,sf,t=0,ReceiveTimeout=0,ButtonTimeout=0,tGPSfull=0,x$,y$,NrSat,temporally$
  DIM Lat=0,Lon=0,Alt=0,Latitude$,Longitude$,Altitude$,AllowMotionSensor=0,HDOPinteger,McastDnctr=0
  DIM payload$="",CMD2RN_LoRaWANini$(43),OnePPS=-1,ChkSum=0,ChkSumEnd=0,CClassMulticast$(5)
  DIM Supctr$,Sdnctr$,Sadr$,Sdr$            ' saving mac parameteres before "sys reset" to assure continuous mac operation used in RNRestart
  DIM SensorCounter=0,CO2dat$,CO2limit=65535,CO2ppm=0
  DIM NumberOfUncnf=NumberOfUncnfInSensorMode,LEDFlash$="G"
  DIM ButtonPressedByApplicationServer=0      ' pushbutton control from application server
  DIM LongSleepTime=LongSleepTimeMin          ' minutes
  DIM PinBat!,BatteryLevelHeader,BatteryLevelPayload
  DIM Mode$="Service",appeui$ LENGTH 16
  DIM GPSpayload$="short"   ' the short GPS payload has only latitude and longitude, altitude the long plus HDOP, temperature and battery voltage
  DIM ShortSleepTimeMin=5   ' at long GPSpayload 15sec, at short GPSpayload 5sec
  DIM ShortSleepTime=5      ' seconds
  DIM DownloadedShortSleeptime=0
  DIM GPSMode$="full"       ' or standby during continuous tracking
  DIM MacTxCnf$="uncnf"     ' application indicates if last mac transmission was cfm or uncfm
  DIM CFilter,MyCFilter,CRed,CGreen,CBlue,NS$,EW$,GPSQuality
  DIM SMI_TEMP,SMI_PRESS     ' measurement values SM1131
  DIM SMI_PRESS_MovingAverage '
  DIM SMIPMA(3)              'SM1131 pressure array to measure average of last four pressure value
  DIM SMIPMAPointer=0
  DIM TH06_TEMP!,TH06_HUMID! ' end TH06
  DIM RSSISNR$,EMBITRX$,EMBITTX$,EMBITTXH$
  DATA "sys reset","mac pause"
  DATA "mac set ch dcycle 0 0","mac set ch drrange 0 0 5","mac set ch status 0 on"
  DATA "mac set ch dcycle 1 0","mac set ch drrange 1 0 5","mac set ch status 1 on"
  DATA "mac set ch dcycle 2 0","mac set ch drrange 2 0 5","mac set ch status 2 on"
  DATA "mac set ch freq 3 867100000","mac set ch dcycle 3 0","mac set ch drrange 3 0 5","mac set ch status 3 on"
  DATA "mac set ch freq 4 867300000","mac set ch dcycle 4 0","mac set ch drrange 4 0 5","mac set ch status 4 on"
  DATA "mac set ch freq 5 867500000","mac set ch dcycle 5 0","mac set ch drrange 5 0 5","mac set ch status 5 on"
  DATA "mac set ch freq 6 867700000","mac set ch dcycle 6 0","mac set ch drrange 6 0 5","mac set ch status 6 on"
  DATA "mac set ch freq 7 867900000","mac set ch dcycle 7 0","mac set ch drrange 7 0 5","mac set ch status 7 on"
  DATA "mac set ch freq 8 868300000","mac set ch dcycle 8 0","mac set ch drrange 8 6 6","mac set ch status 8 on"
  DATA "mac set ch freq 9 868800000","mac set ch dcycle 9 0","mac set ch drrange 9 7 7","mac set ch status 9 on"
  DATA "mac set mcastdevaddr 01DA5110","mac set mcastnwkskey 46126EEEDEAEBCC471EE8FEA7500DB66","mac set mcastappskey 37E5A3A61C9FFE14122F20DAFD232377"
  DATA "mac resume","mac save"
  for i=0 to 43 : READ CMD2RN_LoRaWANini$(i): NEXT i
  DIM Aupctr$,Adnctr$,Aadr$,Adr$,Amode$
  SETTICK 1000,OneSecTick                   ' 1 sec tick time
  VAR RESTORE                               ' without flash initialization this doesn't modify RAM varables
  IF FLASH$="EMPTY" THEN                    ' initializes variables in flash memory, this runs only once
    FLASH$="NO"
    VAR SAVE GPSDeviceID,GPSFormat,SM1131correction,QNH,ReferenceHeight,OnePPSMin,GPSFullOperationTime,MaxTime,NRofDR6
    VAR SAVE NumberOfUncnfInSensorMode,FLASH$,GPSpayload$,ShortSleepTime,LongSleepTime,CO2limit,Programmed$,ShortSleepTimeMin,DownloadedShortSleeptime
  ENDIF
  ? "Micromite ";mm.ver
  ? "Micromite GPS LoRa Mote " fix(Release/100) "v" STR$(Release-100*fix(Release/100),2,0,"0")+Programmed$
  I2C OPEN 100,100
  I2C WRITE MCP9800Addr,0,2,1,&B00000001      ' one-shot default mode to CFG register 7bit signed temperature
  I2C CLOSE
  PIN(SELA)=0
  PIN(SELB)=0
  '  OPEN "COM1:57600" AS #1                        '                         comment & V3 HW
  '  x$=INPUT$(255,#1)                              '                         comment & V3 HW
  '  PIN(RNReset)=1: SETPIN RNReset,DOUT            ' resets RN2483 module    comment & V3 HW
  '  PIN(RNReset)=0:PAUSE 1000                      ' resets RN2483 module    comment & V3 HW
  '  PIN(RNReset)=1                                 ' resets RN2483 module    comment & V3 HW
  '  SETPIN RNReset,OFF                             ' resets RN2483 module    comment & V3 HW
  '  LINE INPUT #1,x$                               '                         comment & V3 HW
  '  ? x$                                           '                         comment & V3 HW
  '  CLOSE #1                                       '                         comment & V3 HW
  PIN(TX1)=0 : SETPIN TX1,DOUT : PAUSE 20
  PIN(TX1)=1 : PAUSE 1
  SETPIN TX1,OFF
  OPEN "COM1:57600" AS #1
  x$=INPUT$(255,#1)
  PRINT #1,"Usys reset":COM1TXEmpty
  WaitsTillRNAnswers
  IF x$="ok" THEN WaitsTillRNAnswers
  GPSON
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' Main:         Service_mode                                '
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ? " "
  ? "  Five second window allows service functions"
  ? " "
  ? "CR/LF to set RN2483, 'PT' PassThrough   mode"
  ? "c to set LoRaWAN channels"
  ? "a appeui setting"
  ? "r or g to toggle red or green leds"
  ? "t to read temperature"
  ? "v to read battery voltage"
  ? "b to check push button with LEDR"
  ? "3 or 4 to read external CO2 sensors"
  ? "s to read external SM1134 sensor"
  ? "h to read external TH06 temperature and humidity sensor"
  ? "l to check L86 GPS/GNSS receiver"
  ? "L LoRa modulation measurement"
  ? "P ping pong P2P range tester"
  ? "E range tester for LoRaEMB"
  ? " "
  t=0
ServiceModes:
  x$= INKEY$
  IF x$<> chr$(13) THEN GOTO ChannelConfig
  x$=INKEY$
  PT
  t=0
  GOTO ServiceModes
ChannelConfig:
  IF x$<>"c" THEN GOTO APPEUI           ' channal configuration of RN2483 modules
  x$=INKEY$
  for i=0 TO 43
    PRINT #1,CMD2RN_LoRaWANini$(i):COM1TXEmpty
    ? CMD2RN_LoRaWANini$(i)                 'DEBUG
    WaitsTillRNAnswers
  NEXT i
  x$=INKEY$
  t=0
ToggleRLED:
  IF x$<>"r" then GOTO ToggleGLED
  x$=INKEY$
  ? "r"
  PIN(LEDR)=NOT PIN(LEDR)
  x$=INKEY$
  t=0
APPEUI:
  IF x$<>"a" THEN GOTO ToggleRLED
  x$=INKEY$
  ? "enter 8 bytes long hex appeui"
  appeui$=ONELINE$()
  IF hex$(val("&H"+appeui$),16)=appeui$ THEN
    ? "mac set appeui "+appeui$
    PRINT #1,"mac set appeui "+appeui$
    PAUSE 10
    LINE INPUT #1,x$
    ? x$
    y$=INPUT$(1,#1)
    ? "mac save"
    PRINT #1,"mac save"
    PAUSE 10
    LINE INPUT #1,x$
    ? x$
    y$=INPUT$(1,#1)
  ELSE
    ? appeui$+" is not 8 bytes long hexa value"
  END IF
  x$=INKEY$
  t=0
ToggleGLED:
  IF x$<>"g" THEN GOTO PulseR
  x$=INKEY$
  ? "g"
  PIN(LEDG)=NOT PIN(LEDG)
  x$=INKEY$
  t=0
PulseR:
  IF x$<>"p" THEN GOTO TempSensor
  x$=INKEY$
  PIN(LEDR)=LEDOFF
  PULSE LEDR,50
  x$=INKEY$
  t=0
TempSensor:
  IF x$<>"t" THEN GOTO VoltageSensor
  x$=INKEY$
  ? STR$(ReadsMCP9800Sensor(),3,1)+" C"
  ? HEX$(ReadsMCP9800Sensor(),2)
  x$=INKEY$
  t=0
VoltageSensor:
  IF x$<> "v" THEN GOTO ButtonTest
  x$=INKEY$
  BatteryLevel
  x$=INKEY$
  t=0
ButtonTest:
  IF x$<>"b" THEN GOTO COM3
  x$=INKEY$
  ? "push button test till ^C"
  DO
    IF  PIN(PUSH)=0 THEN PIN(LEDR)=LEDON ELSE PIN(LEDR)=LEDOFF
  LOOP
COM3:
  IF x$<>"3" THEN GOTO COM4                      ' CO2 sensor on COM3
  LINe INPUT x$
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
    PRINT #3,ONELINE$()
  LOOP
COM4:
  IF x$<>"4" THEN GOTO SM1134Read              ' CO2 sensor on COM4
  LINe INPUT x$
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
    PRINT #4,ONELINE$()
  LOOP
SM1134Read:
  IF x$<>"s" THEN GOTO TH06TEST              ' SM1131
  x$=INKEY$
  RNSleep
  CPU 5
  ? "Reads SM1134 sensors till ^C"
  DO
    PIN(PGC)=0
    PAUSE 2000                            ' test time
    SM1131_TH06
    SensorCounter=SensorCounter+1
    ? STR$(SensorCounter,4);":";DATE$;" ";tiME$;" ";"SMI_TEMP=";STR$(SMI_TEMP/100,3,2);" C SMI_PRESS=";STR$(SMI_PRESS/100,5,2);" hPa"
    PAUSE 10000                           ' relax time
  LOOP
TH06TEST:
  IF x$<>"h" THEN GOTO GPSGNSTEST             ' TH06
  x$=INKEY$
  RNSleep
  CPU 5
  ? "Reads TH06 sensors till ^C"
  DO
    PIN(PGC)=0
    PAUSE 10                               ' test time
    SM1131_TH06
    SensorCounter=SensorCounter+1
    ? STR$(SensorCounter,4);":";DATE$;" ";tiME$;" ";"TH06_TEMP!=";STR$(TH06_TEMP!,3,1)"C";" TH06_HUMID!=";STR$(TH06_HUMID!,3,1);"%"
    PAUSE 1000                             ' relax time
  LOOP
GPSGNSTEST:
  IF x$<>"l" THEN GOTO LoRaModulationTest   ' L86 test
  x$=INKEY$
  ? "Reads GPS sentences till ^C"
  RNSleep
  GPSOPEN
  do
    x$ = input$(1,#2)
    print x$;
  loop
LoRaModulationTest:
  IF x$<>"L" THEN GOTO P2PRangeTest
  x$=INKEY$
  ? "mac pause"
  PRINT #1,"mac pause" : COM1TXEmpty
  WaitsTillRNAnswers
  DO
    f=866900000
    FOR i=0 to 9
      f=f+200000
      ? "radio set freq";f
      PRINT #1,"radio set freq";f;CHR$(13)+CHR$(10); : COM1TXEmpty
      WaitsTillRNAnswers
      IF i<6 THEN sf=i+7 ELSE sf=12
      ? "radio set sf sf";str$(sf)
      PRINT #1,"radio set sf sf";str$(sf) : COM1TXEmpty
      WaitsTillRNAnswers
      ? "radio tx 000102040810204080ff"
      PRINT #1,"radio tx 000102040810204080ff" : COM1TXEmpty
      LINE InPUT #1,x$                                                                      ' doesn't allow interrupt and timeout check
      y$=input$(1,#1)                                                                       ' reads then drops line feed character
      ? x$
      LINE InPUT #1,x$                                                                      ' doesn't allow interrupt and timeout check
      y$=input$(1,#1)                                                                       ' reads then drops line feed character
      ? x$
    next i
  LOOP
P2PRangeTest:
  IF x$<>"P" THEN GOTO LoRaEMB
  x$=INKEY$
  RANDOMIZE val(mid$(time$,7,2)+mid$(time$,4,2)+mid$(time$,1,2))
  ? "mac pause"
  PRINT #1,"mac pause" : COM1TXEmpty
  WaitsTillRNAnswers
  ? "radio set pwr 15"
  PRINT #1,"radio set pwr 15" : COM1TXEmpty
  WaitsTillRNAnswers
  ? "radio set sf sf12"
  PRINT #1,"radio set sf sf12" : COM1TXEmpty
  WaitsTillRNAnswers
  ? "radio set freq 869525000"
  PRINT #1,"radio set freq 869525000" : COM1TXEmpty
  WaitsTillRNAnswers
  DO
    PIN(LEDG)=LEDON
    ? "radio rx 200"
    PRINT #1,"radio rx 200" : COM1TXEmpty
    WaitsTillRNAnswers
    ? "   ";
    WaitsTillRNAnswers
    PIN(LEDG)=LEDOFF
    IF LEFT$(x$,9)<>"radio_err" THEN i=10 ELSE i=20*RND
    PIN(LEDR)=LEDON
    ? "PAUSE ",i
    PAUSE i
    ? "radio tx 00"
    PRINT #1,"radio tx "+hex$(RND*255,2) : COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
    PIN(LEDR)=LEDOFF
  LOOP
LoRaEMB:
  IF x$<>"E" THEN GOTO ENDservice
  ? "mac join abp"
  PRINT #1,"mac join abp" : COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  GPSOFF
  COM1toCOM3
  EMBITTCVR("30")                                             ' Network Stop
  EMBITTCVR("2500")                                           ' Set LoRaEMB
  EMBITTCVR("1103070101")                                     ' Set CH3 (868.500MHz), SF7, BW=250kHz
  EMBITTCVR("2200ff")                                         ' Set Network ID '00FF'
  EMBITTCVR("210003")                                         ' Set Network Address '0003'
  EMBITTCVR("31")                                             ' Network Start
  DO
    Do WHILE PIN(PUSH)=1
    LOOP
    PAUSE 100
    Do WHILE PIN(PUSH)=0
    LOOP
    PAUSE 100
    COM3toCOM1
    ? TIME$ "  mac tx uncnf 10 00"
    PRINT #1,"mac tx uncnf 10 0" : COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
    ? TIME$ "  mac get upctr"
    PRINT #1,"mac get upctr" : COM1TXEmpty
    WaitsTillRNAnswers
    COM1toCOM3
    x$="500000ffff"+hex$(val(x$)-1,8)
    EMBITTCVR(x$)
  LooP
ENDservice:
  IF t<=5 THEN GOTO ServiceModes
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' Main:         GPS_mode                                    '
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ? " "
  ? "The service window is stopped now"
  ? " "
  PIN(PGC)=1                                  ' stops CO2 sensor power
  PIN(LEDR)=LEDOFF
  PIN(LEDG)=LEDOFF
  ? "temparature =" STR$(ReadsMCP9800Sensor(),3,1)+" C"
  ? "battery voltage:",
  BatteryLevel
  t=0
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' RN2483 LoRaWAN init
  ? "mac resume"
  PRINT #1,"mac resume":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac join otaa"                                   ' you may change to abp if you have abp keys
  PRINT #1,"mac join otaa":COM1TXEmpty                ' you may change to abp if you have abp keys
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  IF x$="denied" THEN
    FOR i=1 to 600
      pulse LEDG,5
      pulse LEDR,5
      PAUSE 10
      CPU SLEEP 1
      IF PIN(PUSH)=0 THEN CPU RESTART
    NEXT i
    CPU RESTART
  ENDIF
  TurnOffChannelsDutyCyleControl
  ? "mac save"
  PRINT #1,"mac save":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set dr 0"
  PRINT #1,"mac set dr 0":COM1TXEmpty
  WaitsTillRNAnswers
  RNSleep
  Mode$="GPS"
  PIN(PGC)=0
  BatteryLevel
  CO2Measure
  SM1131_TH06
  SensorPayloadToLoRaWAN
  VariablesToLoRaWAN
GPSMode:
  tGPSfull=0
  AllowMotionSensor=1
  CPU 5
  GPSON
  Mode$="GPS"
  SETPIN WAKEUP,INTH,WakeupInt
  SETPIN PPS,INTH,PPSInt,PULLUP
  OnePPS=-1
  PAUSE 200
WaitsForPPS:
  IF t<MaxTime THEN GOTO WaitsForPPS2
  GPSOPEN
  GPS2BACKUP
  GPSOFF
  SETPIN WAKEUP,OFF
  ? "CPU sleeps till awaken up by motion sensor or button" 'DEBUG
  SETTICK 0,OneSecTick                      ' 1 sec tick timeer off
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  PIN(PGC)=1
  CPU SLEEP
  ? "CPU awake again" 'DEBUG
  SETTICK 1000,OneSecTick                   ' 1 sec tick timer on again
  PIN(PGC)=0
  CO2Measure
  SM1131_TH06
  SensorPayloadToLoRaWAN
  VariablesToLoRaWAN
  t=0
  ? t
  GOTO GPSMode
WaitsForPPS2:
  IF PIN(PUSH)=0 THEN GOTO ModeChangeByButton
  IF ButtonPressedByApplicationServer<>0 THEN GOTO ModeChangeByServer
  IF OnePPS=0 THEN PIN(PGC)=0
  IF OnePPS<OnePPSMin THEN GOTO WaitsForPPS
  SM1131_TH06
  PIN(PGC)=1
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
  TIME$ = left$(arg$(1),2) + ":" + MID$(arg$(1),3,2) + ":" + MID$(arg$(1),5,2)                              ' Micromite TIME$ syncronized to GPS
  Lat=(val(mid$(arg$(2),1,2))*600000+val(mid$(arg$(2),3,2))*10000+val(mid$(arg$(2),6,4)))*8388608\54000000  'ASCII GPS coordinates coding to 24bit/16bit binaries
  IF arg$(3)="S" THEN Latitude$=HEX$(-Lat AND &Hffffff,6) ELSE Latitude$=HEX$(Lat,6)
  IF arg$(3)="S" THEN NS$="1" ELSE NS$="0"
  Lon=(val(MID$(arg$(4),1,3))*600000+val(MID$(arg$(4),4,2))*10000+val(MID$(arg$(4),7,4)))*8388608\108000000
  IF arg$(5)="W" THEN Longitude$=HEX$(-Lon AND &Hffffff,6) ELSE Longitude$=HEX$(Lon,6)
  IF arg$(5)="W" THEN EW$="1" ELSE EW$="0"
  Alt=VAL(arg$(9)) AND 65535                                   ' Altitude
  If Alt>40000 THEN Altitude$=HEX$(0,4) ELSE Altitude$=HEX$(Alt,4)
  NrSat=VAL(arg$(7))                                  ' number of satellites
  IF HDOPinteger=<50 THEN GPSQuality= 16
  IF 50<HDOPinteger and HDOPinteger<100 THEN GPSQuality=32
  IF HDOPinteger>=100 THEN GPSQuality=48
  IF NrSat>=15 THEN GPSQuality=GPSQuality+15 ELSE GPSQuality=GPSQuality+NrSat
  ? arg$(7)+"sat UT"+TIME$ 'DEBUG
  CPU 10
  RNWakeup
  MacTxCnf$="uncnf"
  IF GPSFormat=3 THEN                              'Adeunis GPS format
    payload$="mac tx uncnf 1 d2"+HEX$(ReadsMCP9800Sensor(),2)+MID$(arg$(2),1,4)+MID$(arg$(2),6,3)+NS$
    payload$=payload$+MID$(arg$(4),1,5)+MID$(arg$(4),7,2)+EW$+HEX$(BatteryLevelHeader*700/254+3500,4)
    payload$=payload$+HEX$(GPSQuality,2)
    goto SendBothGPS
  endif
  IF GPSFormat=4 THEN                              'Adeunis legacy GPS format
    payload$="mac tx uncnf 1 d2"+HEX$(ReadsMCP9800Sensor(),2)+MID$(arg$(2),1,4)+MID$(arg$(2),6,3)+NS$
    payload$=payload$+MID$(arg$(4),1,5)+MID$(arg$(4),7,2)+EW$+HEX$(BatteryLevelHeader*700/254+3500,4)
    goto SendBothGPS
  endif
  IF GPSFormat=2 THEN                              'Semtech GPS format
    payload$="mac tx uncnf 2 00000000000000"+HEX$(BatteryLevelHeader,2)+Latitude$+Longitude$+Altitude$
    goto SendBothGPS
  endif
  payload$="mac tx uncnf 202 "+Latitude$+Longitude$+Altitude$
  IF GPSFormat=1 THEN
    payload$=payload$+HEX$(INT((QNH*100-(SMI_PRESS+SM1131correction))/12.1513),4)+HEX$(QNH,4)
    payload$=payload$+HEX$(HDOPinteger,2)+HEX$(ReadsMCP9800Sensor(),2)+HEX$(BatteryLevelPayload,2)+left$(arg$(1),6)
  ENDIF
SendBothGPS:
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
  Process05
  IF NRofDR6=0 THEN
    ? "mac set dr 0"
    PRINT #1,"mac set dr 0":COM1TXEmpty
    WaitsTillRNAnswers
  END IF
  DR6counter=NRofDR6
  RNSleep
  temporally$=payload$
  VariablesToLoRaWAN
  payload$=temporally$
  PAUSE 5000
  RNWakeup
SendGPSPayload2:
  ? payload$ 'DEBUG
  IF NOT EOF(#0) THEN
    IF ONELINE$()="PT" THEN PT
  END If
  LEDFlash$="R"                                       ' 1sec red LED flashing till end of transmission
  PRINT #1,payload$ : COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  payload$="mac set bat "+str$(BatteryLevelHeader)
  ? payload$
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  RNSleep
  CPU 5
  IF CO2limit<10000 THEN
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
  END IF
  IF CO2ppm>CO2Limit THEN                             ' 1sec bip on CO2ppm frequency
    ? "bip-bip" 'DEBUG
    SETPIN PGD,OFF
    SETPIN PGC,OFF
    SETPIN LVP,OFF
    PWM 1,CO2ppm,25,100,75
    PAUSE 1000
    pwm 1,STOP
    PIN(PGD)=1: SETPIN PGD,DOUT
    PIN(PGC)=1: SETPIN PGC,DOUT
    PIN(LVP)=1: SETPIN LVP,DOUT
  ENDIF
  ? "CPU sleeps ShortSleepTime =";ShortSleepTime;"sec. Left active time ="; MaxTime-t
  SETTICK 0,OneSecTick                   ' 1 sec tick timeer off
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  SETPIN PPS,OFF
  '  SETPIN WAKEUP,OFF
  '  PIN(WAKEUP)=0:SETPIN WAKEUP,DOUT
  CPU Sleep ShortSleepTime
  LEDFlash$="G"
  BatteryLevel
  SETPIN WAKEUP,OFF
  SETPIN WAKEUP,INTH,WakeupInt
  ? "CPU awake again" 'DEBUG
  SETTICK 1000,OneSecTick                   ' 1 sec tick timer on again
  GPSOPEN
  GPSStandby2Full
  SETPIN WAKEUP,INTH,WakeupInt
  SETPIN PPS,INTH,PPSInt,PULLUP
  OnePPS=-1
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
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
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
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
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
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
    SensorPayloadToLoRaWAN
    VariablesToLoRaWAN
    tGPSfull=0
    GOTO GPSMode
  ENDIF
  IF ButtonTimeout<4 THEN
    PIN(LEDR)=LEDOFF
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
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
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' Main:         Sensor_mode                                 '
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
ChangeToSensor:
  ? "change to Sensor mode" 'DEBUG
  NumberOfUncnf=NumberOfUncnfInSensorMode
  Mode$="Sensor"
  PIN(FORCE)=0                        'switch off GPS receiver
  PIN(GPSPWR)=1
  CPU 10
  RNWakeup
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
  PAUSE 10000
  IF x$="mac_tx_ok" THEN
    GetRSSIandSNR
    ? "mac tx cnf 2 "+RSSISNR$ 'DEBUG
    PRINT #1,"mac tx cnf 2 "+RSSISNR$:COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
  ELSE
    ? "mac tx cnf 1 01" 'DEBUG
    PRINT #1,"mac tx cnf 1 01":COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
  ENDIF
  IF x$="mac_tx_ok" THEN
    GetRSSIandSNR
    ? "mac tx uncnf 3 "+RSSISNR$ 'DEBUG
    PRINT #1,"mac tx uncnf 3 "+RSSISNR$:COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
  ENDIF
  ? "mac get dr" 'DEBUG
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  RNSleep
  AllowMotionSensor=0
SensorMode:
  IF CO2limit=65534 THEN
    NumberOfUncnf=NumberOfUncnf-1                     'Sensor beacon mode
    ? "NumberOfUncnf=",NumberOfUncnf
    VariablesToLoRaWAN
    RNWakeup
    LEDFlash$="R"
    payload$="mac tx uncnf 202 "+Latitude$+Longitude$
    ? "mac get dnctr"
    PRINT #1,"mac get dnctr":COM1TXEmpty
    WaitsTillRNAnswers
    payload$=payload$+hex$(val(x$),8)
    NumberOfUncnf=NumberOfUncnf-1
    ? "NumberOfUncnf=",NumberOfUncnf
    ? payload$
    PRINT #1,payload$:COM1TXEmpty
    WaitsTillRNAnswers
    WaitsTillRNAnswers
    RNSleep
    PAUSE 500
    CPU 5
    LEDFlash$="G"
  ENDIF
  i=LongSleepTime
SensorMode1:
  ? "CPU sleeps ";i;" minutes" 'DEBUG
  PIN(LEDG)=LEDOFF
  Pin(LEDR)=LEDOFF
  CPU SLEEP 58
  PAUSE 500
  IF PIN(PUSH)=0 THEN GOTO ChangeToGPSMode
  If ButtonPressedByApplicationServer=2 THEN GOTO ChangeToGPSMode
  If ButtonPressedByApplicationServer=4 THEN
    ButtonPressedByApplicationServer=0
    PIN(FORCE)=0                        'switch off GPS receiver
    PIN(GPSPWR)=1
    CPU 10
    GOTO Multicast
  ENDIF
  IF i=1 or CO2limit<10000 THEN
    PIN(PGC)=0
    CO2Measure
    SM1131_TH06
  ENDIF
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
  SETPIN WAKEUP,OFF
  PIN(GPSPWR)=0
  PIN(FORCE)=1
  CPU 10
  RNWakeup
  ? "mac set adr off"
  PRINT #1,"mac set adr off":COM1TXEmpty
  WaitsTillRNAnswers
  RNRestart
  RNSLeep
  ButtonPressedByApplicationServer=0
  AllowMotionSensor=1
  t=0
  tGPSfull=0
  GOTO GPSMode
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' Main:         Multicast_mode                              '
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
Multicast:                                   ' controlling RGB LED by C Class RGB messages
  AllowMotionSensor=0
  RNWakeup
  AMode$=Mode$
  ? "mac set adr on"
  PRINT #1,"mac set adr on":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set class c"
  PRINT #1,"mac set class c":COM1TXEmpty
  WaitsTillRNAnswers
  PRINT #1,"mac set dr 5":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac tx cnf 4 00"
  PRINT #1,"mac tx cnf 4 00":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  GetRSSIandSNR
  PAUSE 10000
  ? "mac tx cnf 4 01"
  PRINT #1,"mac tx cnf 4 01":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  GetRSSIandSNR
  PAUSE 2000
  ? "mac tx uncnf 4 02"
  PRINT #1,"mac tx uncnf 4 02":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  PAUSE 2000
  ? "mac tx uncnf 4 03"
  PRINT #1,"mac tx uncnf 4 03":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  PAUSE 2000
  ? "mac tx uncnf 4 04"
  PRINT #1,"mac tx uncnf 4 04":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  MyCFilter=CFilter
  ? "MyCFilter=",MyCFilter
  ? "mac set mcast on"
  PRINT #1,"mac set mcast on":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set mcastdnctr 0"
  PRINT #1,"mac set mcastdnctr 0":COM1TXEmpty
  WaitsTillRNAnswers
  Mode$="Multicast"
  DO
    IF NOT EOF(#0) THEN
      IF ONELINE$()="PT" THEN PT
      EXIT DO
    END If
    IF PIN(PUSH)=0 THEN
      PIN(LEDG)=LEDON
      DO WHILE PIN(PUSH)=0
      LOOP
      PIN(LEDG)=LEDOFF
      EXIT DO
    ENDIF
    IF EOF(#1)=0 THEN
      WaitsTillRNAnswers
      ? time$ 'DEBUG
    END IF
    IF CFilter=0 AND ButtonPressedByApplicationServer=4 THEN
      ButtonPressedByApplicationServer=0
      PAUSE 5000*RND()+100
      ? "mac tx uncnf 210 "+RiGHT$(x$,10)+RSSISNR$
      PRINT #1,"mac tx uncnf 210 "+RiGHT$(x$,10)+RSSISNR$:COM1TXEmpty
      WaitsTillRNAnswers
      WaitsTillRNAnswers
      EXIT DO
    ENDIF
    IF CFilter=MyCFilter AND ButtonPressedByApplicationServer=4 THEN
      PWM 1,200,100-CRed,100-CBlue,100-CGreen
      ButtonPressedByApplicationServer=0
      PAUSE 5000*RND()+100
      ? "mac tx uncnf 210 "+RiGHT$(x$,10)+RSSISNR$
      PRINT #1,"mac tx uncnf 210 "+RiGHT$(x$,10)+RSSISNR$:COM1TXEmpty
      WaitsTillRNAnswers
      WaitsTillRNAnswers
      ? "mac get dnctr"
      PRINT #1,"mac get dnctr":COM1TXEmpty
      WaitsTillRNAnswers
      ? "mac get mcastdnctr"
      PRINT #1,"mac get mcastdnctr":COM1TXEmpty
      WaitsTillRNAnswers
      GetRSSIandSNR
    ENDIF
  LOOP
  ? "mac get dnctr"
  PRINT #1,"mac get dnctr":COM1TXEmpty
  WaitsTillRNAnswers
  Adnctr$=x$
  ? "mac get upctr"
  PRINT #1,"mac get upctr":COM1TXEmpty
  WaitsTillRNAnswers
  Aupctr$=x$
  ? "mac get dr"
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  Adr$=x$
  ? "sys reset"                                                 ' sets back A class operation
  PRINT #1,"sys reset":COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set dnctr " Adnctr$
  PRINT #1,"mac set dnctr " Adnctr$:COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac set upctr " Aupctr$
  PRINT #1,"mac set upctr " Aupctr$:COM1TXEmpty
  WaitsTillRNAnswers
  IF AMode$="GPS" THEN Adr$="0"
  ? "mac set dr " Adr$
  PRINT #1,"mac set dr " Adr$:COM1TXEmpty
  WaitsTillRNAnswers
  IF AMode$="GPS" THEN Aadr$="off" ELSE Aadr$="on"
  ? "mac set adr " Aadr$
  PRINT #1,"mac set adr " Aadr$:COM1TXEmpty
  WaitsTillRNAnswers
  Mode$=AMode$
  pwm 1,STOP
  PIN(PGD)=1: SETPIN PGD,DOUT
  PIN(PGC)=1: SETPIN PGC,DOUT
  PIN(LVP)=1: SETPIN LVP,DOUT
  ? "mac join abp"
  PRINT #1,"mac join abp":COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  RNSLeep
  ButtonPressedByApplicationServer=0
  AllowMotionSensor=1
  IF Mode$="GPS" THEN GOTO GPSMode
  AllowMotionSensor=0
  GOTO SensorMode
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '               Interrupt routines                          '
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB OneSecTick
  IF LEDFlash$="G" THEN pulse LEDG,5 ELSE PULSE LEDR,5
  ReceiveTimeout=ReceiveTimeout+1
  ButtonTimeout=ButtonTimeout+1
  If Mode$="GPS" THEN
    tGPSfull=tGPSfull+1
    t=t+1
  ENDIF
  IF Mode$="Service" THEN   t=t+1
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB WakeupInt                                         ' motion sensor
  IF AllowMotionSensor=0 THEN EXIT SUB
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
  PAUSE 50
  SensorCounter=SensorCounter+1
  CO2dat$ = INPUT$(100, #3)
  ? STR$(SensorCounter,4);":";DATE$;" ";tiME$;" ";CO2dat$; 'DEBUG
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RxCO2Int4
  PAUSE 50
  SensorCounter=SensorCounter+1
  CO2dat$ = INPUT$(100, #4)
  ? STR$(SensorCounter,4);":";DATE$;" ";tiME$;" ";CO2dat$; 'DEBUG
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '                                 functions                                  '
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
  ' ONELINE$() Reads one line from consol port while allows interrupt during maximum 60 seconds
FUNCTION ONELINE$()
  LOCAL y$
  LOCaL x$
  LOCAL RTO
  x$=""
  RTO=ReceiveTimeout
ConsoleTerminal:
  IF ReceiveTimeout>=(RTO+60) THEN
    ONELINE$=""
    ? "console input timeout"
    EXIT FUNCTION
  END IF
  y$=INKEY$
  IF y$="" THEN GOTO ConsoleTerminal
  x$=x$+y$
  if y$<>chr$(13) THEN GOTO ConsoleTerminal
  ONELINE$=left$(x$,LEN(x$)-1)
  ? ONELINE$
END FUNCTION
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' EMBIT binary to hexa format
FUNCTION B2H$(Binary$)
  Local H$="",i
  FOR i=1 TO LEN(Binary$)
    H$=H$+HEX$(ASC(MID$(Binary$,i,1)),2)
  NEXT i
  '  ? "Hexa$=" H$
  B2H$=H$
END Function
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' EMBIT hexa to binary format
FUNCTION H2B$(Hexa$)
  LOCAL B$,i,CheckSum=0
  '  ? "Hexa$=" Hexa$
  b$=CHR$((LEN(Hexa$)/2+3)\256)+CHR$(LEN(Hexa$)/2+3-(LEN(Hexa$)/2+3)\256*256)   ' length
  FOR i=1 TO LEN(Hexa$)/2
    B$=B$+CHR$(val("&H"+MID$(Hexa$,2*i-1,1))*16+val("&H"+MID$(Hexa$,2*i,1)))
  NEXT i                                                                        ' instruction + payload
  FOR i=1 TO LEN(Hexa$)/2+2
    CheckSum=CheckSum+ASC(MID$(b$,i,1))
  next i
  CheckSum=CheckSum AND 255
  b$=b$+CHR$(CheckSum)                                                          ' checksum
  H2B$=B$
END Function
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  '                                 subroutines                                '
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
  ' subroutine reads GPS sentence into arg$() array
SUB GetGPSRecord
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
        i=20
        Exit DO
      ENDIF
      arg$(i) = arg$(i) + x$                        ' add to the data
    LOOP                                            ' keep going
    '      ? "   i=";i;">";arg$(i); 'DEBUG
  NEXT i                                            ' increment the field
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNSleep                                               ' RN2483 to sleep mode
  PRINT #1,"sys sleep 4294967296":COM1TXEmpty  'RN2483 sleep
  PIN(SELA)=1
  PIN(SELB)=1
  CLOSE #1
  PIN(TX1)=1 : SETPIN TX1,DOUT
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNWakeup                                           ' wakes up RN2483
  RN2483OPEN
  PRINT #1,"Usys get ver":COM1TXEmpty
  WaitsTillRNAnswers
  IF x$="ok" THEN WaitsTillRNAnswers
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RN2483OPEN                                        ' OPENS COM1 port for RN2483
  PIN(SELA)=0
  PIN(SELB)=0
  PIN(TX1)=0
  PAUSE 20
  PIN(TX1)=1
  PAUSE 20
  SETPIN TX1,OFF
  OPEN "COM1:57600" AS #1
  x$=INPUT$(255,#1)
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
  PIN(TX1)=1: SETPIN TX1,DOUT
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GPSFull2Standby
  IF tGPSfull<=GPSFullOperationTime THEN
    GPSMode$="full"
    GPSCLOSE
    exit sub
  END IF
  PRINT #2,"$PMTK161,0*28":COM2TXEmpty
  GPSMode$="standby"
  GPSCLOSE
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GPSStandby2Full
  IF GPSMode$="full" THEN
    GPSCLOSE
    exit SUB
  END IF
  PRINT #2,"$PMTK101*32":COM2TXEmpty  ' hot start
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
  payload$="mac tx "
  IF Mode$="GPS" THEN
    payload$=payload$+"uncnf"
    MacTxCnf$="uncnf"
    GOTO SensorPayload
  ENDIF
  NumberOfUncnf=NumberOfUncnf-1
  IF NumberOfUncnf>0 THEN
    payload$=payload$+"uncnf"
    MacTxCnf$="uncnf"
    GOTO SensorPayload
  ENDIF
  NumberOfUncnf=NumberOfUncnfInSensorMode
  payload$=payload$+"cnf"
  MacTxCnf$="cnf"
SensorPayload:
  BatteryLevel
  payload$=payload$+" 209 "+HEX$(ReadsMCP9800Sensor(),2)+HEX$(BatteryLevelPayload,2)    ' internal sensor data
  IF MID$(CO2dat$,2,1)="Z" THEN                                                         ' external COZIR with only CO2 sensor
    payload$=payload$+HEX$(VAL(MID$(CO2dat$,4,5)),4)+"000000"
    GOTO EndCOZIR
  ENDIF
  IF MID$(CO2dat$,18,1)="Z" THEN                                                        ' external COZIR with H and T
    payload$=payload$+HEX$(VAL(MID$(CO2dat$,20,5)),4)+HEX$(VAL(MID$(CO2dat$,4,5)),4)+RIGHT$(HEX$((VAL(MID$(CO2dat$,12,5))-1000)\10,2),2)
    GOTO EndCOZIR
  ENDIF
  payload$=payload$+"0000000000"
EndCOZIR:                                                                               ' external SM1131 and TH06
  payload$=payload$+HEX$(SMI_TEMP/100 AND 255,2)+HEX$(SMI_PRESS,6)+HEX$(TH06_TEMP!\1 AND 255,2)+HEX$(TH06_HUMID!*10\1 AND 65535,4)
  CPU 10
  RNWakeup
  ? "NumberOfUncnf=",NumberOfUncnf
  ? STR$(SMI_TEMP/100,3,2);" C SMI_PRESS=";STR$(SMI_PRESS/100,5,2);" hPa";"   ";"TH06_TEMP!=";STR$(TH06_TEMP!,3,1)"C";" TH06_HUMID!=";STR$(TH06_HUMID!,3,1);"%"
  ? payload$ 'DEBUG
  IF NOT EOF(#0) THEN
    IF ONELINE$()="PT" THEN PT
  END If
  LEDFlash$="R"
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  payload$="mac set bat "+str$(BatteryLevelHeader)
  ? payload$
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  ? "mac get dr"
  PRINT #1,"mac get dr":COM1TXEmpty
  WaitsTillRNAnswers
  LEDFlash$="G"
  RNSleep
  CPU 5
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB CO2Measure
  PAUSE 1000          ' 1 secend COZIR power setup time is required for accurate one_shot measurement
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
  CLOSE #3
  PIN(SELA)=1
  PIN(SELB)=1
  PIN(TX1)=1: SETPIN TX1,DOUT
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
  IF x$="invalid_param" THEN
    x$=""
    EXIT SUB
  ENDIF
  IF x$="not_joined" THEN
    x$=""
    EXIT SUB
  ENDIF
  IF x$="no_free_ch" THEN
    x$=""
    EXIT SUB
  ENDIF
  IF x$="silent" THEN
    PRINT #1,"mac forceENABLE"COM1TXEMPTY
    CPU RESTART
    EXIT SUB
  ENDIF
  IF x$="frame_counter_err_rejoin_needed" THEN
    CPU RESTART
    EXIT SUB
  ENDIF
  IF x$="mac_paused" THEN
    x$=""
    EXIT SUB
  ENDIF
  IF x$="busy" THEN
    x$=""
    EXIT SUB
  ENDIF
  IF x$="invalid_data_len" THEN
    x$=""
    EXIT SUB
  ENDIF
  If Mode$="Multicast" THEN ReceiveTimeout=-5 ELSE ReceiveTimeout=-120
  Do WHILE EOF(#1)                                                                       ' allows interrupt before line input
    If ReceiveTimeout>=0 THEN
      x$=Mode$+" RN Module UART Timeout"
      ? x$
      EXIT SUB
    ENDIF
  LOOP
  LOCAL LF$
  LINE InPUT #1,x$                                                                       ' doesn't allow interrupt and timeout check
  LF$=input$(1,#1)                                                                       ' reads then drops line feed character
  ? x$
  IF x$="busy" THEN RNRestart
  if len(x$)<>21 THEN EXIT SUB
  IF LEFT$(x$,11)<>"mac_rx 209 " THEN EXIT SUB
  IF VAL(MID$(x$,12,2))=>6 THEN EXIT SUB                                                  ' returns if not valid downlink message arrived
  ButtonPressedByApplicationServer=VAL(MID$(x$,12,2))                                    ' push button control from application server
  IF ButtonPressedByApplicationServer=5 THEN GOTO RXINT5
  IF ButtonPressedByApplicationServer=4 THEN GOTO RXINT4
  IF ButtonPressedByApplicationServer=3 THEN GOTO RXINT3
  DownloadedShortSleeptime=VAL("&H"+MID$(x$,14,2))
  ShortSleepTime=DownloadedShortSleeptime+ShortSleepTimeMin                              ' seconds
  LongSleepTime=VAL("&H"+MID$(x$,16,2))+LongSleepTimeMin                                 ' minutes
  CO2limit=VAL("&H"+MID$(x$,18,4))
RXEnds:
  ? "ButtonPressedByApplicationServer=",ButtonPressedByApplicationServer
  ? "GPSpayload$=";GPSpayload$
  ? "ShortSleepTime=";ShortSleepTime;" seconds" 'DEBUG
  ? "LongSleepTime=";LongSleepTime;" minutes" 'DEBUG
  ? "CO2limit=";CO2limit;" ppm" 'DEBUG
  ? "ReferenceHeight=";ReferenceHeight
  ? "QNH=";QNH
  ? "SM1131correction=";SM1131correction
  VAR SAVE GPSDeviceID,GPSFormat,SM1131correction,QNH,ReferenceHeight,OnePPSMin,GPSFullOperationTime,MaxTime,NRofDR6
  VAR SAVE NumberOfUncnfInSensorMode,FLASH$,GPSpayload$,ShortSleepTime,LongSleepTime,CO2limit,Programmed$,ShortSleepTimeMin,DownloadedShortSleeptime
  EXIT SUB
RXINT3:
  ButtonPressedByApplicationServer=0
  ReferenceHeight=VAL("&h"+MID$(x$,14,4))
  QNH=VAL("&h"+MID$(x$,18,4))
  IF ReferenceHeight=0 THEN GOTO RXEnds
  SM1131correction=100*QNH-ReferenceHeight/0.082296-SMI_PRESS_MovingAverage
  GOTO RXEnds
RXINT4:
  CFilter=VAL(MID$(x$,14,2))
  ? "CFilter=",CFilter
  CRed=VAL(MID$(x$,16,2))
  ? "CRed=",CRed
  CGreen=VAL(MID$(x$,18,2))
  ? "CGreen=",CGreen
  CBlue=VAL(MID$(x$,20,2))
  ? "CBlue=",CBlue
  EXIT SUB
RXINT5:
  ButtonPressedByApplicationServer=0
  IF Mode$="GPS" THEN
    Downlink05$=x$
    EXIT SUB
  ENDIF
  Process05
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB Process05
  GPSDeviceID=VAL("&H"+MID$(x$,14,1))
  GPSFormat=VAL("&H"+MID$(x$,15,1))
  IF GPSFormat=0 THEN ShortSleepTimeMin=5                                                'short MICROMITE MOTE GPS payload
  IF GPSFormat=1 THEN ShortSleepTimeMin=15                                               'long MICROMITE MOTE GPS payload
  ShortSleepTime=DownloadedShortSleeptime+ShortSleepTimeMin                              ' seconds
  OnePPSMin=VAL("&H"+MID$(x$,16,1))
  IF VAL("&H"+MID$(x$,17,1))=0 THEN GPSFullOperationTime=60 ELSE GPSFullOperationTime=60*VAL("&H"+MID$(x$,17,1))
  IF VAL("&H"+MID$(x$,18,2))=0 THEN MaxTime=60 ELSE MaxTime=60*VAL("&H"+MID$(x$,18,2))
  NRofDR6=VAL("&H"+MID$(x$,20,1))
  IF VAL("&H"+MID$(x$,21,1))=0 THEN NumberOfUncnfInSensorMode=4 ELSE NumberOfUncnfInSensorMode=4*VAL("&H"+MID$(x$,21,1))
  VAR SAVE GPSDeviceID,GPSFormat,SM1131correction,QNH,ReferenceHeight,OnePPSMin,GPSFullOperationTime,MaxTime,NRofDR6
  VAR SAVE NumberOfUncnfInSensorMode,FLASH$,GPSpayload$,ShortSleepTime,LongSleepTime,CO2limit,Programmed$,ShortSleepTimeMin,DownloadedShortSleeptime
  ? MID$(x$,12,10)
  ? "GPSDeviceID=";GPSDeviceID
  ? "GPSFormat=";GPSFormat
  ? "OnePPSMin=";OnePPSMin
  ? "GPSFullOperationTime=";GPSFullOperationTime
  ? "MaxTime=";MaxTime
  ? "NRofDR6=";NRofDR6
  ? "NumberOfUncnfInSensorMode=";NumberOfUncnfInSensorMode
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB RNRestart
  PRINT #1,"mac get upctr":COM1TXEmpty
  LINE InPUT #1,Supctr$
  ? "upctr="+Supctr$
  PRINT #1,"mac get dnctr":COM1TXEmpty
  LINE InPUT #1,Sdnctr$
  ? "dnctr="+Sdnctr$
  PRINT #1,"mac get adr":COM1TXEmpty
  LINE InPUT #1,Sadr$
  ? "adr="+Sadr$
  PRINT #1,"mac get dr":COM1TXEmpty
  LINE InPUT #1,Sdr$
  ? "dr="+Sdr$
  ? "sys reset"
  PRINT #1,"sys reset":COM1TXEmpty
  LINE InPUT #1,x$
  ? x$
  ? "mac join abp"
  PRINT #1,"mac join abp":COM1TXEmpty
  LINE InPUT #1,x$
  ? x$
  LINE InPUT #1,x$
  ? x$
  PRINT #1,"mac set upctr "+Supctr$:COM1TXEmpty
  ? "mac set upctr "+Supctr$
  LINE InPUT #1,x$
  ? x$
  PRINT #1,"mac set dnctr "+Sdnctr$:COM1TXEmpty
  ? "mac set dnctr "+Sdnctr$
  LINE InPUT #1,x$
  ? x$
  PRINT #1,"mac set adr "+Sadr$:COM1TXEmpty
  ? "mac set adr "+Sadr$
  LINE InPUT #1,x$
  ? x$
  PRINT #1,"mac set dr "+Sdr$:COM1TXEmpty
  ? "mac set dr "+Sdr$
  LINE InPUT #1,x$
  ? x$
  x$="busy"
END SUB
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB PT                                                 ' Consol to RN Module PassThrough for debugging
  ? "RN2483 manual setup till ^C or 'quit' "
  DO
    IF NOT EOF(#0) THEN
      LINE INPUT x$
      IF x$="quit" THEN END SUB
      PRINT #1,x$
    END IF
    IF NOT EOF(#1) THEN
      LINE INPUT #1,x$
      ? x$
      y$=INPUT$(1,#1)
    END IF
  LOOP
  ''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB VariablesToLoRaWAN
  payload$="mac tx uncnf 203 "+HEX$(GPSDeviceID,1)+HEX$(GPSFormat,1)+HEX$(OnePPSMin,1)+HEX$(GPSFullOperationTime/60,1)+HEX$(MaxTime/60,2)
  payload$=payload$+HEX$(NRofDR6,1)+HEX$(NumberOfUncnfInSensorMode/4,1)+HEX$(DownloadedShortSleeptime,2)+HEX$(LongSleepTime-1,2)
  payload$=payload$+HEX$(CO2limit,4)
  IF Release<1000 THEN payload$=payload$+"0"+STR$(Release) ELSE payload$=payload$+STR$(Release)
  PAUSE 5000
  CPU 10
  RNWakeup
  ? payload$ 'DEBUG
  LEDFlash$="R"
  PRINT #1,payload$:COM1TXEmpty
  WaitsTillRNAnswers
  WaitsTillRNAnswers
  RNSleep
  PAUSE 500
  CPU 5
  LEDFlash$="G"
END SUB
  '''''''''''''''''''''''''  reads SM1131 then TH06  ''''''''''''''''''''''''''''
SUB SM1131_TH06                     'DRK 2017.03.28
  LOCAL ROB(4),REGOB(2),i
  I2C OPEN 100, 100
  I2C WRITE &H6C,1,1,&H2E           'READING 2EH-37H AREA
  I2C READ &H6C,0,4,ROB()           'DSP_T,DSP_S,STAT_SYNC,XXX,STATUS
  SMI_TEMP=(ROB(1)<<8)+(ROB(0))     'BIN
  SMI_TEMP=(SMI_TEMP-7500)/1.5      '0.01C
  SMI_PRESS=(ROB(3)<<8)+(ROB(2))    'BIN
  SMI_PRESS=(SMI_PRESS+8800)/0.22   'Pa
  if SMI_TEMP=-5000 and SMI_PRESS=40000 then
    SMI_TEMP=0
    SMI_PRESS=100000
  endif
  I2C WRITE &H40,1,1,&H0E5           'HUMIDITY READINGS
  PAUSE 10
  I2C READ &H40,0,2,REGOB()
  TH06_HUMID!=(REGOB(0)<<8)+(REGOB(1))
  I2C WRITE &H40,1,1,&H0E0             'AND THE TEMPERATURE
  I2C READ &H40,0,2,REGOB()
  TH06_TEMP!=(REGOB(0)<<8)+(REGOB(1))
  TH06_HUMID!=(125.0*TH06_HUMID!)/65536.0-6.0 'CALCULATIONS (SEE DATASHEET)
  TH06_TEMP!=(175.72*TH06_TEMP!)/65536.0-46.85
  IF TH06_HUMID!=-6 AND TH06_TEMP!=-46.85 THEN
    TH06_TEMP!=0
    TH06_HUMID!=0
  ENDIF
  I2C CLOSE
  PIN(PGC)=1                        ' COM3 3.3V off
  SMIPMA(SMIPMAPointer)=SMI_PRESS
  IF SMIPMAPointer<3 THEN SMIPMAPointer=SMIPMAPointer+1 ELSE SMIPMAPointer=0
  SMI_PRESS_MovingAverage=0
  FOR i=0 to 3
    SMI_PRESS_MovingAverage=SMI_PRESS_MovingAverage+SMIPMA(i)
  NEXT i
  SMI_PRESS_MovingAverage=SMI_PRESS_MovingAverage/4
  ? "SMI_PRESS_MovingAverage=" SMI_PRESS_MovingAverage "  SMI_PRESS=" SMI_PRESS 'DEBUG
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB GetRSSIandSNR
  PRINT #1,"mac pause":COM1TXEmpty
  WaitsTillRNAnswers
  PRINT #1,"radio get rssi":COM1TXEmpty
  WaitsTillRNAnswers
  RSSISNR$=""
  X2RSSISNR
  PRINT #1,"radio get snr":COM1TXEmpty
  WaitsTillRNAnswers
  X2RSSISNR
  PRINT #1,"mac resume":COM1TXEmpty
  WaitsTillRNAnswers
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB X2RSSISNR
  IF val(x$)<0 THEN RSSISNR$=RSSISNR$+"1" ELSE RSSISNR$=RSSISNR$+"0"
  IF ABS(val(x$))>=100 THEN RSSISNR$=RSSISNR$+"1" ELSE RSSISNR$=RSSISNR$+"0"
  IF ABS(val(x$))<=9 THEN RSSISNR$=RSSISNR$+"0" ELSE RSSISNR$=RSSISNR$+LEFT$(RIGHT$(x$,2),1)
  RSSISNR$=RSSISNR$+RIGHT$(x$,1)
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB COM1toCOM3                                                                    'EMBIT
  CLOSE #1
  PIN(SELA)=0
  PIN(SELB)=1
  OPEN "COM1:9600" AS #3
  EMBITRX$=INPUT$(255,#3)
  EMBITRX$=""
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB COM3toCOM1                                                                    'EMBIT
  CLOSE #3
  PIN(SELA)=0
  PIN(SELB)=0
  OPEN "COM1:57600" AS #1
  X$=INPUT$(255,#1)
  X$=""
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB EMBITTCVR(Hexa$)                                                              'EMBIT
  LOCAL RxBufferLength
  EMBITTX$=H2B$(Hexa$)
  ? Time$ "  H>M:" B2H$(EMBITTX$)
  PRINT #3,EMBITTX$;
  Do WHILE EOF(#3)
  LOOP
  PAUSE 2                                                                         ' waits the second byte
  EMBITRX$=INPUT$(2,#3)
  RxBufferLength=ASC(MID$(EMBITRX$,1,1))*256+ASC(MID$(EMBITRX$,2,1))-2
  EMBITRX$=EMBITRX$+INPUT$(RxBufferLength,#3)
  EMBITRX$=B2H$(EMBITRX$)
  ? TIME$ "  M>H:" EMBITRX$
END SUB
  '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
SUB TurnOffChannelsDutyCyleControl                                               ' turns off LNS DutyCycle control after OTAA
  LOCAL i                                                                        ' user still responsible to assure 1% transmit ducty cycle of the MOTE
  FOR i=0 TO 7
  ? "mac set ch dcycle";i;" 0"
  PRINT #1,"mac set ch dcycle";i;" 0":COM1TXEmpty  
  WaitsTillRNAnswers
  NEXT i
End SUB