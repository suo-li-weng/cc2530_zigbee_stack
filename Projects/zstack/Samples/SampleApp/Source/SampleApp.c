/*********************************************************************
 * INCLUDES
 */
#include <stdio.h>
#include <string.h>
#include "AF.h"
#include "OnBoard.h"
#include "OSAL_Tasks.h"
#include "SampleApp.h"
#include "ZDApp.h"
#include "ZDObject.h"
#include "ZDProfile.h"

#include "hal_drivers.h"
#include "hal_key.h"
#if defined ( LCD_SUPPORTED )
  #include "hal_lcd.h"
#endif
#include "hal_led.h"
#include "hal_uart.h"
#include "ds18b20.h"
#include "hal_adc.h"
#include "mfrc522.h"
/*********************************************************************
 * MACROS
 */
#define COORD_ADDR   0x00
#define ED_ADDR      0x01
#define UART0        0x00
#define MAX_NODE     0x04
#define UART_DEBUG   0x00        //调试宏,通过串口输出协调器和终端的IEEE、短地址
#define LAMP_PIN     P0_4        //定义P0.4口为继电器输入端
#define GAS_PIN      P0_5
#define COME_MSG     0x31

#define RFID_COME    0x01
#define EP_COME      0x02
#define EP_LIVE      0x02
#define MSG_END      0x23


#define LCD_FLASH_MS 700
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof(arr)[0])

//---------------------------------------------------------------------
//标准版不同的终端需要修改此ID,用于识别协调器发过来的数据，ID相同则处理
//专业版自动从Flash获得地址，所有终端固件相同，适合量产
static uint16 EndDeviceID = 0x0004; //终端ID，重要
//---------------------------------------------------------------------



/*********************************************************************
 * CONSTANTS
 */



#if !defined( SAMPLE_APP_PORT )
#define SAMPLE_APP_PORT  0
#endif

#if !defined( SAMPLE_APP_BAUD )
  #define SAMPLE_APP_BAUD  HAL_UART_BR_115200
#endif

// When the Rx buf space is less than this threshold, invoke the Rx callback.
#if !defined( SAMPLE_APP_THRESH )
#define SAMPLE_APP_THRESH  64
#endif

#if !defined( SAMPLE_APP_RX_SZ )
#define SAMPLE_APP_RX_SZ  128
#endif

#if !defined( SAMPLE_APP_TX_SZ )
#define SAMPLE_APP_TX_SZ  128
#endif

// Millisecs of idle time after a byte is received before invoking Rx callback.
#if !defined( SAMPLE_APP_IDLE )
#define SAMPLE_APP_IDLE  6
#endif

// Loopback Rx bytes to Tx for throughput testing.
#if !defined( SAMPLE_APP_LOOPBACK )
#define SAMPLE_APP_LOOPBACK  FALSE
#endif

// This is the max byte count per OTA message.
#if !defined( SAMPLE_APP_TX_MAX )
#define SAMPLE_APP_TX_MAX  80
#endif

#define SAMPLE_APP_RSP_CNT  4

// This list should be filled with Application specific Cluster IDs.
const cId_t SampleApp_ClusterList[SAMPLE_MAX_CLUSTERS] =
{
  SAMPLEAPP_P2P_CLUSTERID,
  SAMPLEAPP_PERIODIC_CLUSTERID,
};

const SimpleDescriptionFormat_t SampleApp_SimpleDesc =
{
  SAMPLEAPP_ENDPOINT,              //  int   Endpoint;
  SAMPLEAPP_PROFID,                //  uint16 AppProfId[2];
  SAMPLEAPP_DEVICEID,              //  uint16 AppDeviceId[2];
  SAMPLEAPP_DEVICE_VERSION,        //  int   AppDevVer:4;
  SAMPLEAPP_FLAGS,                 //  int   AppFlags:4;
  SAMPLE_MAX_CLUSTERS,          //  byte  AppNumInClusters;
  (cId_t *)SampleApp_ClusterList,  //  byte *pAppInClusterList;
  SAMPLE_MAX_CLUSTERS,          //  byte  AppNumOutClusters;
  (cId_t *)SampleApp_ClusterList   //  byte *pAppOutClusterList;
};

endPointDesc_t SampleApp_epDesc =
{
  SAMPLEAPP_ENDPOINT,
 &SampleApp_TaskID,
  (SimpleDescriptionFormat_t *)&SampleApp_SimpleDesc,
  noLatencyReqs
};

/*********************************************************************
 * TYPEDEFS
 */
typedef unsigned int  uint;
/*********************************************************************
 * GLOBAL VARIABLES
 */
devStates_t SampleApp_NwkState;   
uint8 SampleApp_TaskID;           // Task ID for internal task/event processing.
//int sum = 0;
static uint8 SampleApp_State;           //状态标识
static bool SampleApp_Alarm_Switch = 0;
char Lcd_Buf[17];                    //LCD缓冲

//TODO:去除不必要的变量
#ifdef ZDO_COORDINATOR
uint8 Node_Data[MAX_NODE][6];         //终端数据缓冲区 0=温度 1=温度小数 2=气体 3=报警器 4=状态
unsigned long int Time_Sec;           //时间分钟数
bool Node_Check_Alive[MAX_NODE];            //设备在线
bool Node_Alived[MAX_NODE];            //设备在线

bool Card_Come[MAX_NODE]={0};       //新卡到达标记
uint8 Card_Buff[MAX_NODE][6];    //卡号缓冲区


//LCD相关
static uint8 Lcd_New_Data;              //LCD刷新标记
int SampleApp_Connected;         //终端在线数
uint8 SampleApp_Key_Pressed;     //按键按下
uint8 SampleApp_Alarm_Area;      //报警终端编号
static bool Lcd_Update;          //新消息是否通知



//开启警报
static unsigned char CLOSE_ALARM[] = {0x3A, 0xFF, 0xFF, 0x0A, 0x00, 0x30, 0x23};
//关闭警报
static unsigned char OPEN_ALARM[] = {0x3A, 0xFF, 0xFF, 0x0A, 0x01, 0x31, 0x23};

unsigned char Uart_Buf[20];

#else

/////////////////////////////rfid定义////////////////////
//M1卡的某一块写为如下格式，则该块为钱包，可接收扣款和充值命令
//4字节金额（低字节在前）＋4字节金额取反＋4字节金额＋1字节块地址＋1
//字节块地址取反＋1字节块地址＋1字节块地址取反 
unsigned char data2[4]  = {0x12,0,0,0};
unsigned char DefaultKey[6] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}; 
unsigned char g_ucTempbuf[20];    
unsigned char MLastSelectedSnr[4];
unsigned char RevBuffer[30];  
unsigned char SerBuffer[20]; 
unsigned char CmdValid; 
unsigned char waitCommData=1;
int data_len=0;
int data_index=0;

static bool SendFlag = 0;

#endif
/*********************************************************************
 * EXTERNAL VARIABLES
 */

/*********************************************************************
 * EXTERNAL FUNCTIONS
 */
extern void Delay_us(unsigned int );

/*********************************************************************
 * LOCAL VARIABLES
 */

static uint8 SampleApp_MsgID;

afAddrType_t SampleApp_Periodic_DstAddr; //广播
afAddrType_t SampleApp_Flash_DstAddr;    //组播
afAddrType_t SampleApp_P2P_DstAddr;      //点播


//static afAddrType_t SampleApp_TxAddr;
//static uint8 SampleApp_TxSeq;
static uint8 SampleApp_TxBuf[SAMPLE_APP_TX_MAX+1];
static uint8 SampleApp_TxLen;

//static afAddrType_t SampleApp_RxAddr;
//static uint8 SampleApp_RxSeq;
//static uint8 SampleApp_RspBuf[SAMPLE_APP_RSP_CNT];

/*********************************************************************
 * LOCAL FUNCTIONS
 */

static void SampleApp_ProcessMSGCmd( afIncomingMSGPacket_t *pkt );
void SampleApp_CallBack(uint8 port, uint8 event); 
static void SampleApp_Send_P2P_Message( void );
static void packDataAndSend(uint8 fc, uint8* data, uint8 len);


//TODO:整改
uint8 TxBuffer[128];
void PrintAddrInfo(uint16 shortAddr, uint8 *pIeeeAddr);
uint8 GetDataLen(uint8 fc);
void AfSendAddrInfo(void);
void GetIeeeAddr(uint8 * pIeeeAddr, uint8 *pStr);
uint8 XorCheckSum(uint8 * pBuf, uint8 len);
char NumberToLetter(unsigned char number);
uint8 GetMq2();
#ifdef ZDO_COORDINATOR
static void SampleApp_Send(void);
//查询终端数据
uint8 SendData(uint8 addr, uint8 FC);
void SetBuzzer(uint8 on);
#define PinBuzzer P0_7
#define GetBuzzer (PinBuzzer?0:1)
static void SampleApp_Check_Alive();
static void SampleApp_LCD_Display();
static bool SampleApp_SendDataToEndDevice(uint8* data, int len);
#else
void findCard();
void iccardcode();
#define PinRelay P0_4
#define GetRelay (PinRelay?0:1)
void SetRelay(uint8 on);

void PrintfRfidCard(uint8* data, int len);
#endif

void Delay_ms(uint Time)//n ms延时
{
  while(Time--)
  {
    Delay_us(1000);
  }
}

void rfid_init()
{
  // IC_SDA P1_4
  P1DIR |= 1<<4;
  P1INP |= 1<<4;
  P1SEL &= ~(1<<4);
  
  // IC_SCK  P1_5
  P1DIR |= 1<<5;
  P1INP |= 1<<5;
  P1SEL &= ~(1<<5);
  
  // IC_MOSI P1_6
  P1DIR |= 1<<6;
  P1INP |= 1<<6;
  P1SEL &= ~(1<<6);
  
  // IC_MISO P2_1
  P2DIR |= 1<<1;
  P2INP |= 1<<1;
  P2SEL &= ~(1<<1);  

  // IC_RST P2_2
  P2DIR &= ~(1<<2);
  P2INP &= ~(1<<2);
  P2SEL &= ~(1<<2);
  
  MF522_SCK = 1;
  MF522_NSS = 1;
  CmdValid=0; 
  PcdReset();
  PcdAntennaOff(); 
  PcdAntennaOn();  
  M500PcdConfigISOType( 'A' );
}

/*********************************************************************
 * @fn      SampleApp_Init
 *
 * @brief   This is called during OSAL tasks' initialization.
 *
 * @param   task_id - the Task ID assigned by OSAL.
 *
 * @return  none
 */
void SampleApp_Init( uint8 task_id )
{
  halUARTCfg_t uartConfig;

  SampleApp_TaskID = task_id;
  //SampleApp_RxSeq = 0xC3;
  SampleApp_NwkState = DEV_INIT;       
#ifdef ZDO_COORDINATOR
  MT_UartInit();                  //串口初始化
  MT_UartRegisterTaskID(task_id); //注册串口任务
#endif
  afRegister( (endPointDesc_t *)&SampleApp_epDesc );
  RegisterForKeys( task_id );

  
#ifdef ZDO_COORDINATOR
  //协调器初始化
  
  //逢蜂鸣器初始化
  
  //TODO：增加人体感应和光照感应
  P0SEL &= ~0x80;                 //设置P07为普通IO口
  P0DIR |= 0x80;                 //P07定义为输出口

  //默认蜂鸣器不响
  SetBuzzer(0);
  
#else

  P0SEL &= ~0x10;                 //设置P04为普通IO口
  P0DIR |= 0x10;                 //P04定义为输出口

  //默认继电器关
  SetRelay(0);
  
  P0SEL &= ~0x20;                 //设置P0.5为普通IO口
  P0DIR &= ~0x20;                 //P0.5定义为输入口
  
  P0SEL &= 0x7f;                  //P0_7配置成通用io
  
  rfid_init();
#endif
  
  SampleApp_Periodic_DstAddr.addrMode = (afAddrMode_t)AddrBroadcast;//广播
  SampleApp_Periodic_DstAddr.endPoint = SAMPLEAPP_ENDPOINT;
  SampleApp_Periodic_DstAddr.addr.shortAddr = 0xFFFF;

  // Setup for the flash command's destination address - Group 1
  SampleApp_Flash_DstAddr.addrMode = (afAddrMode_t)afAddrGroup;//组播
  SampleApp_Flash_DstAddr.endPoint = SAMPLEAPP_ENDPOINT;
  SampleApp_Flash_DstAddr.addr.shortAddr = SAMPLEAPP_FLASH_GROUP;
  
  SampleApp_P2P_DstAddr.addrMode = (afAddrMode_t)Addr16Bit; //点播 
  SampleApp_P2P_DstAddr.endPoint = SAMPLEAPP_ENDPOINT; 
  SampleApp_P2P_DstAddr.addr.shortAddr = 0x0000;            //发给协调器
  
#ifdef ZDO_COORDINATOR
    
    osal_start_timerEx( SampleApp_TaskID,
                        SAMPLEAPP_LCD_DISPLAY_EVT,
                        LCD_FLASH_MS );
    osal_start_timerEx( SampleApp_TaskID,
                        SAMPLEAPP_TIME_SEC_EVT,
                        1000 );
    
    osal_start_timerEx( SampleApp_TaskID,
                        SAMPLEAPP_CHECK_ALIVE_EVT,
                        5000 );
    
#endif
    
  
}


void SampleApp_HandleKeys( uint8 shift, uint8 keys )
{
  (void)shift;  // Intentionally unreferenced parameter
  
  //SampleApp_Key_Pressed++;
  if ( keys & HAL_KEY_SW_1 )//key1
  {
    #ifdef ZDO_COORDINATOR
    SampleApp_Key_Pressed = 2;
    Lcd_New_Data = 1;
    #else
    LAMP_PIN = ~LAMP_PIN;
    #endif
  }

  
  if ( keys & HAL_KEY_SW_6 )//key2
  {
    #ifdef ZDO_COORDINATOR  
    SampleApp_Key_Pressed = 1;
    Lcd_New_Data = 1;
    #else
    findCard();
   #endif
  }

}



bool SampleApp_SendDataToEndDevice(uint8* data, int len)
{
    if(data==NULL)
    {
    return false;
    }

    if ( AF_DataRequest( &SampleApp_Periodic_DstAddr, &SampleApp_epDesc,
                         SAMPLEAPP_PERIODIC_CLUSTERID,
                         len,
                         data,
                         &SampleApp_MsgID,
                         AF_DISCV_ROUTE,
                         AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
    {
      return true;
    }
    else
    {
      return false;
    }
}



/*********************************************************************
 * @fn      SampleApp_ProcessEvent
 *
 * @brief   Generic Application Task event processor.
 *
 * @param   task_id  - The OSAL assigned task ID.
 * @param   events   - Bit map of events to process.
 *
 * @return  Event flags of all unprocessed events.
 */
UINT16 SampleApp_ProcessEvent( uint8 task_id, UINT16 events )
{
  (void)task_id;  // Intentionally unreferenced parameter
  if ( events & SYS_EVENT_MSG )
  {
    afIncomingMSGPacket_t *MSGpkt;
    while ( (MSGpkt = (afIncomingMSGPacket_t *)osal_msg_receive( SampleApp_TaskID )) )
    {
      switch ( MSGpkt->hdr.event )
      {
        case KEY_CHANGE://按键事件
          SampleApp_HandleKeys( ((keyChange_t *)MSGpkt)->state, ((keyChange_t *)MSGpkt)->keys );
          break;
        
      case AF_INCOMING_MSG_CMD:
        SampleApp_ProcessMSGCmd( MSGpkt );
        break;
        
      case ZDO_STATE_CHANGE:
        SampleApp_NwkState = (devStates_t)(MSGpkt->hdr.status);
        if ( (SampleApp_NwkState == DEV_ZB_COORD)||
            (SampleApp_NwkState == DEV_ROUTER)
            || (SampleApp_NwkState == DEV_END_DEVICE) )
        {
            #if defined(ZDO_COORDINATOR) //协调器通过串口输出自身短地址、IEEE  
                    #if UART_DEBUG
                    PrintAddrInfo( NLME_GetShortAddr(), aExtendedAddress + Z_EXTADDR_LEN - 1);
                    #endif
                    Lcd_New_Data = 1;
                #else                        //终端无线发送短地址、IEEE   
                    AfSendAddrInfo();
                    //联网成功启动周期性上报事件
                    osal_start_timerEx( SampleApp_TaskID,
                              SAMPLEAPP_SEND_PERIODIC_MSG_EVT,
                              SAMPLEAPP_SEND_PERIODIC_MSG_TIMEOUT );
                #endif
        }
        else
        {
          // Device is no longer in the network
        }
        break;

      default:
        break;
      }

      osal_msg_deallocate( (uint8 *)MSGpkt );
    }

    return ( events ^ SYS_EVENT_MSG );
  }
  
  
  
  #if defined(ZDO_COORDINATOR)
  
  //检查在线终端数量
    if ( events & SAMPLEAPP_CHECK_ALIVE_EVT )
    {
        SampleApp_Check_Alive();
        osal_start_timerEx( SampleApp_TaskID, SAMPLEAPP_CHECK_ALIVE_EVT,
            5000 );
        return (events ^ SAMPLEAPP_CHECK_ALIVE_EVT);
    }
    if ( events & SAMPLEAPP_TIME_SEC_EVT )
    {
        ++Time_Sec;
        osal_start_timerEx( SampleApp_TaskID, SAMPLEAPP_TIME_SEC_EVT,
            1000 );
        
        return (events ^ SAMPLEAPP_TIME_SEC_EVT);
    }
    //刷新LCD
    if ( events & SAMPLEAPP_LCD_DISPLAY_EVT )
    {
        SampleApp_LCD_Display();
        
        osal_start_timerEx( SampleApp_TaskID, SAMPLEAPP_LCD_DISPLAY_EVT,
            (LCD_FLASH_MS + (osal_rand() & 0x00FF)) );
        
        return (events ^ SAMPLEAPP_LCD_DISPLAY_EVT);
    }
  
    #endif
  
  if ( events & SAMPLEAPP_SEND_PERIODIC_MSG_EVT )
  {
    //终端上传到协调器
    SampleApp_Send_P2P_Message();

    // Setup to send message again in normal period (+ a little jitter)
    osal_start_timerEx( SampleApp_TaskID, SAMPLEAPP_SEND_PERIODIC_MSG_EVT,
        (SAMPLEAPP_SEND_PERIODIC_MSG_TIMEOUT + (osal_rand() & 0x00FF)) );

    // return unprocessed events
    return (events ^ SAMPLEAPP_SEND_PERIODIC_MSG_EVT);
  }


  return ( 0 );  // Discard unknown events.
}

/*********************************************************************
 * @fn      SampleApp_ProcessMSGCmd
 *
 * @brief   Data message processor callback. This function processes
 *          any incoming data - probably from other devices. Based
 *          on the cluster ID, perform the intended action.
 *
 * @param   pkt - pointer to the incoming message packet
 *
 * @return  TRUE if the 'pkt' parameter is being used and will be freed later,
 *          FALSE otherwise.
 */
void SampleApp_ProcessMSGCmd( afIncomingMSGPacket_t *pkt )
{
  #if defined(ZDO_COORDINATOR)
    uint16 shortAddr;
    uint8 *pIeeeAddr;
  #endif
    uint8 afRxData[30]={0};
    uint8 afDataLen=0;

  
  switch ( pkt->clusterId )
  {
#if defined(ZDO_COORDINATOR)
  // 接收终端上传的数据
  case SAMPLEAPP_P2P_CLUSTERID: 
    {
      uint8 FC;
      uint8 len = 4;
      uint8 checksum = 0;
      afDataLen = pkt->cmd.DataLength;
      osal_memcpy(afRxData, pkt->cmd.Data, pkt->cmd.DataLength);
      
      switch(afRxData[0]) //简单协议命令字解析
      {

        case 0x3B:  //收到终端无线发过来的短地址和IEEE地址,通过串口输出显示      
            shortAddr=(afRxData[1]<<8)|afRxData[2];
            pIeeeAddr = &afRxData[3];
            #if UART_DEBUG
            PrintAddrInfo(shortAddr, pIeeeAddr + Z_EXTADDR_LEN - 1);
            #endif   
        break;
    case 0x3A:
            FC = afRxData[3];
            len += GetDataLen(FC); 
            checksum = XorCheckSum(afRxData, len);
            //接收数据正确返回相应数据
            if(checksum == afRxData[len] && afRxData[len+1] == 0x23)
            {
                if(FC == 0x02) //收到终端传过来的传感器数据并保存
                {  
                    Node_Data[afRxData[2]-1][0] = afRxData[4];
                    Node_Data[afRxData[2]-1][1] = afRxData[5];
                    Node_Data[afRxData[2]-1][2] = afRxData[6];
                    Node_Data[afRxData[2]-1][3] = afRxData[7];
                    Node_Data[afRxData[2]-1][4] = afRxData[8];
                    Node_Data[afRxData[2]-1][5] = 0x00;
                    if(afRxData[8])
                    {
                      SampleApp_State = afRxData[8];
                      SampleApp_Alarm_Area = afRxData[2];
                      SetBuzzer(1);
                      Lcd_New_Data = 1;
                    }
                    else if(Lcd_Update)
                    {
                      Lcd_New_Data = 1;
                    }
                    #if UART_DEBUG
                    HalUARTWrite (UART0, Node_Data[afRxData[2]-1], 5); //调试时通过串口输出
                    #endif   
                }
                else if(FC == 0x09) //RFID信息
                {
                  if(afDataLen==12)
                  {
                    //HalLcdWriteString( "error", HAL_LCD_LINE_4 );
                      osal_memcpy(Card_Buff[afRxData[2]-1], afRxData+4, 6);
                      Card_Come[afRxData[2]-1] = 1;
                  }
                  
                  Uart_Buf[0] = COME_MSG;
                  osal_memcpy(Uart_Buf+1, afRxData+1, 2);
                  Uart_Buf[3] = RFID_COME;
                  Uart_Buf[4] = XorCheckSum(Uart_Buf, 4);
                  Uart_Buf[5] = MSG_END;
                  HalUARTWrite (UART0, Uart_Buf, 6);
                  
                  #if UART_DEBUG
                  HalUARTWrite (UART0, Card_Buff[afRxData[2]-1], 6); //调试时通过串口输出
                  #endif  
                }
            }
           
           break;
        case 0x3C: //心跳包
           Node_Check_Alive[afRxData[2]-1] = 1;
           break;

        default:
            break;
        }
        break;
    }
    break;
#else
  case SAMPLEAPP_PERIODIC_CLUSTERID://终端消息
    {
      afDataLen = pkt->cmd.DataLength;
      osal_memcpy(afRxData, pkt->cmd.Data, pkt->cmd.DataLength);
      
      case 0x3A:  //开关灯设备          
      if(afRxData[3] == 0x0A || afRxData[3] == 0x0B || afRxData[3] == 0x0C) //控制终端          
      {
          if(EndDeviceID == afRxData[2] || afRxData[2]==0xFF)
          {
            SetRelay(afRxData[4]);
            if(!afRxData[4])
            {
                SampleApp_State = 0;
            }
          }
          break;
      }
    }
    break;
#endif
    default:
      break;
  }
}


/*********************************************************************
 * @fn      SampleApp_CallBack
 *
 * @brief   Send data OTA.
 *
 * @param   port - UART port.
 * @param   event - the UART port event flag.
 *
 * @return  none
 */
void SampleApp_CallBack(uint8 port, uint8 event)
{
  (void)port;
  if ((event & (HAL_UART_RX_FULL | HAL_UART_RX_ABOUT_FULL | HAL_UART_RX_TIMEOUT)) &&
#if SAMPLE_APP_LOOPBACK
      (SampleApp_TxLen < SAMPLE_APP_TX_MAX))
#else
      !SampleApp_TxLen)
#endif
  {
#if defined(ZDO_COORDINATOR)
    SampleApp_Send();
#endif
  }
}


/*********************************************************************
* @fn      SampleApp_Send
*
* @brief   Send data OTA.
*
* @param   none
*
* @return  none
*/
#if defined(ZDO_COORDINATOR)
//串口数据处理
static void SampleApp_Send(void)
{

    uint8 len=0, addr, FC;
    uint8 checksum=0;
    
#if SERIAL_APP_LOOPBACK
    if (SampleApp_TxLen < SERIAL_APP_TX_MAX)
    {
        SampleApp_TxLen += HalUARTRead(SERIAL_APP_PORT, SampleApp_TxBuf+SampleApp_TxLen+1,
            SERIAL_APP_TX_MAX-SampleApp_TxLen);
    }
    
    if (SampleApp_TxLen)
    {
        (void)SampleApp_TxAddr;
        if (HalUARTWrite(SERIAL_APP_PORT, SampleApp_TxBuf+1, SampleApp_TxLen))
        {
            SampleApp_TxLen = 0;
        }
        else
        {
            osal_set_event(SampleApp_TaskID, SAMPLEAPP_SEND_EVT);
        }
    }
#else
    if (!SampleApp_TxLen && 
        (SampleApp_TxLen = HalUARTRead(UART0, SampleApp_TxBuf, SAMPLE_APP_TX_MAX)))
    {
        if (SampleApp_TxLen)
        {
            SampleApp_TxLen = 0;
            if(SampleApp_TxBuf[0] == 0x3A)
            {
                addr = SampleApp_TxBuf[2];
                FC = SampleApp_TxBuf[3];
                len = GetDataLen(FC); 
                len += 4;
                checksum = XorCheckSum(SampleApp_TxBuf, len);
                //接收数据正确返回相应数据
                if(checksum == SampleApp_TxBuf[len] && SampleApp_TxBuf[len+1] == 0x23)
                {
                    if(FC == 0x0A || FC == 0x0B || FC == 0x0C) //控制终端
                    {                            
                      if (SampleApp_SendDataToEndDevice(SampleApp_TxBuf, len+2))
                        {
                          if(SampleApp_TxBuf[4])
                          {
                            SampleApp_State = 1;
                            SampleApp_Alarm_Switch = 1;
                          }
                          else
                          {
                            SampleApp_Alarm_Switch = 0;
                            SampleApp_State = 0;
                            SampleApp_Alarm_Area = 0;
                            //Lcd_Page = 0;
                            //SampleApp_Function_Index = 0;
                          }
                            //HalUARTWrite(UART0, SampleApp_TxBuf, len+2); //无线发送成功后原样返回给上位机  
                            //osal_set_event(SampleApp_TaskID, SAMPLEAPP_SEND_EVT);
                        }
                        else  //暂时没发现错误，关闭终端发送也正常。无线发送失败后将数据位和校验位置0返给上位机    
                        {
                            SampleApp_TxBuf[len-1] = 0x00;
                            SampleApp_TxBuf[len] = 0x00;
                            HalUARTWrite(UART0, SampleApp_TxBuf, len+2);
                        }
                    }
                    else
                    {
                        if(addr == 0xff)
                        {
                          FC = 0x01;
                        }
            SendData(addr, FC);   //查询操作
                    }
        }
            }
    }
    }
#endif

}
#endif

float old_temp = 25;
uint8 old_mq2; 
/*********************************************************************
 * @fn      SampleApp_Send_P2P_Message
 *
 * @brief   point to point.
 *
 * @param   none
 *
 * @return  none
 */
void SampleApp_Send_P2P_Message( void )
{
  #if defined(ZDO_COORDINATOR)
    #else
    float temp;
    uint8 SendBuf[15]={0};
    
    //发送心跳包
    SendBuf[0] = 0x3C;                          
    SendBuf[1] = HI_UINT16( EndDeviceID );
    SendBuf[2] = LO_UINT16( EndDeviceID );
    SendBuf[3] = XorCheckSum(SendBuf, 3);
    SendBuf[4] = 0x23;

    //无线发送到协调器
    if ( AF_DataRequest( &SampleApp_P2P_DstAddr, &SampleApp_epDesc,
                       SAMPLEAPP_P2P_CLUSTERID,
                       5,
                       SendBuf,
                       &SampleApp_MsgID,
                       AF_DISCV_ROUTE,
                       AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
    {
    }
    else
    {
    // Error occurred in request to send.
    }
    
    //发送其他数据
    SendBuf[0] = 0x3A;                          
    SendBuf[1] = HI_UINT16( EndDeviceID );
    SendBuf[2] = LO_UINT16( EndDeviceID );
    SendBuf[3] = 0x02;                       //FC
    
    temp = floatReadDs18B20();

    SendBuf[4] = (int)temp;
    SendBuf[5] = (int)( (temp - SendBuf[4]) * 10 );
    SendBuf[6] = GetMq2();  //获取气体传感器的状态
    
    if(temp > 40 || GAS_PIN?0:1)
    {
        SendBuf[8] = 1;
    }
    else
    {
        float t = temp - old_temp;
        old_temp = temp;
        int q = SendBuf[6] - old_mq2;
        old_mq2 = SendBuf[6];
        if(t > 1.0 || q > 3)
        {
          SendBuf[8] = 2;
        }
        else
        {
          SendBuf[8] = 0;
        }
    }
    if(SendBuf[8] != SampleApp_State)
    {
      SampleApp_State = SendBuf[8];
      if(SampleApp_State == 1)
      {
        SetRelay(1);
      }
    }
    sprintf(Lcd_Buf, "状态：%d", SampleApp_State);
    HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_3 );
    SendBuf[7] = GetRelay; //获得报警器的状态
    SendBuf[9] = XorCheckSum(SendBuf, 9);
    SendBuf[10] = 0x23;
  
    if ( AF_DataRequest( &SampleApp_P2P_DstAddr, &SampleApp_epDesc,
                       SAMPLEAPP_P2P_CLUSTERID,
                       11,
                       SendBuf,
                       &SampleApp_MsgID,
                       AF_DISCV_ROUTE,
                       AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
    {
    // Successfully requested to be sent.
    }
    else
    {
    // Error occurred in request to send.
    }
#endif
}

#if defined(ZDO_COORDINATOR)
#else
void findCard()
{
  uint8 SendBuf[15]={0};
  bool error = 0;
  int cnt = 0;
  //寻卡命令
  RevBuffer[0]=0x02;
  RevBuffer[1]=0x26;
  
  do
  {
    // 寻卡
    iccardcode();
    ++cnt;
  }while(RevBuffer[1] && cnt < 20);
  
  
  
  if(RevBuffer[1]==0)//寻卡成功
  {
      //发送卡片信息
      SendBuf[0] = 0x3A;                          
      SendBuf[1] = HI_UINT16( EndDeviceID );
      SendBuf[2] = LO_UINT16( EndDeviceID );
      SendBuf[3] = 0x09;                       //FC
      //读卡命令
      SendBuf[4]=RevBuffer[2];  //data
      SendBuf[5]=RevBuffer[3];  //data        

      //找到卡
      //读卡
      RevBuffer[0]=0x03;
      iccardcode();

      if(RevBuffer[1]==0)
      {
          //读卡成功
          //记录卡ID
          SendBuf[6]=RevBuffer[2];  //data
          SendBuf[7]=RevBuffer[3];  //data
          SendBuf[8]=RevBuffer[4];  //data
          SendBuf[9]=RevBuffer[5];  //data
      }
      else
      {
          error=1;
      }
  }
  else
  {
    HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
    Delay_ms(500);
    HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
    Delay_ms(500);
    HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
    Delay_ms(500);
    HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
    error=1;
  }

  if(!error)
  {
       //输出显示
      PrintfRfidCard(SendBuf+4, 6);
      SendBuf[10] = XorCheckSum(SendBuf, 10);
      SendBuf[11] = 0x23;
      if ( AF_DataRequest( &SampleApp_P2P_DstAddr, &SampleApp_epDesc,
                     SAMPLEAPP_P2P_CLUSTERID,
                     12,
                     SendBuf,
                     &SampleApp_MsgID,
                     AF_DISCV_ROUTE,
                     AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
      {
          // Successfully requested to be sent.
          HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
          Delay_ms(500);
          HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
      }
      else
      {
          // Error occurred in request to send.
      }
  }
}


//LCD和串口显示RFID信息
void PrintfRfidCard(uint8* data, int len)
{
    char Card_Buff[20]={0};
    char error=0;

    if(data[0]==0x44 && data[1]==0x00)
    {
        HalLcdWriteString( "Mifare_UltraLight", HAL_LCD_LINE_3 );
        HalUARTWrite (UART0, (uint8 *)"Mifare_UltraLight", strlen("Mifare_UltraLight"));
    }
    else if(data[0]==0x04 && data[1]==0x00)
    {
        HalLcdWriteString( "Mifare_One(S50)", HAL_LCD_LINE_3 );
        HalUARTWrite (UART0, (uint8 *)"Mifare_One(S50)", strlen("Mifare_One(S50)"));
    }
    else if(data[0]==0x02 && data[1]==0x00)
    {
        HalLcdWriteString( "Mifare_One(S70)", HAL_LCD_LINE_3 );
        HalUARTWrite (UART0, (uint8 *)"Mifare_One(S70)", strlen("Mifare_One(S70)"));
    }
    else if(data[0]==0x08 && data[1]==0x00)
    {
        HalLcdWriteString( "Mifare_One(X)", HAL_LCD_LINE_3 );
        HalUARTWrite (UART0, (uint8 *)"Mifare_One(X)", strlen("Mifare_One(X)"));
    }
    else if(data[0]==0x44 && data[1]==0x03)
    {
        HalLcdWriteString( "Mifare_DESFire", HAL_LCD_LINE_3 );
        HalUARTWrite (UART0, (uint8 *)"Mifare_DESFire", strlen("Mifare_DESFire"));
    }
    else
    {
        error=1;
        HalLcdWriteString( "", HAL_LCD_LINE_3 );
        HalLcdWriteString( "", HAL_LCD_LINE_4 );
        HalUARTWrite (UART0, (uint8 *)"find error", strlen("find error"));
    }


    if(error!=1)
    {
        Card_Buff[0]='I';
        Card_Buff[1]='D';
        Card_Buff[2]=':';
        for(int i=0; i<4; i++)
        {
            unsigned char temp= data[2+i];
            Card_Buff[3+i*2]=NumberToLetter((temp>>4)&0x0f);
            Card_Buff[3+i*2+1]=NumberToLetter(temp&0x0f);
        }

        HalLcdWriteString( Card_Buff, HAL_LCD_LINE_4 );
        HalUARTWrite (UART0, (uint8 *)Card_Buff, strlen(Card_Buff));
    }

}
#endif
//通过串口输出短地址 IEEE
void PrintAddrInfo(uint16 shortAddr, uint8 *pIeeeAddr)
{
    uint8 strIeeeAddr[17] = {0};
    char  buff[30] = {0};    
    
    //获得短地址   
    sprintf(buff, "shortAddr:%04X   IEEE:", shortAddr);  
 
    //获得IEEE地址
    GetIeeeAddr(pIeeeAddr, strIeeeAddr);

    HalUARTWrite (UART0, (uint8 *)buff, strlen(buff));
    Delay_ms(10);
    HalUARTWrite (UART0, strIeeeAddr, 16); 
    HalUARTWrite (UART0, "\n", 1);
}

//终端发送短地址
void AfSendAddrInfo(void)
{
    uint16 shortAddr;
    uint8 strBuf[11]={0};  
    
    shortAddr=NLME_GetShortAddr();
    
    strBuf[0] = 0x3B;                          //发送地址给协调器 可用于点播
    strBuf[1] = HI_UINT16( shortAddr );        //存放短地址高8位
    strBuf[2] = LO_UINT16( shortAddr );        //存放短地址低8位
    
    osal_memcpy(&strBuf[3], NLME_GetExtAddr(), 8);
  if ( AF_DataRequest( &SampleApp_P2P_DstAddr, &SampleApp_epDesc,
                       SAMPLEAPP_P2P_CLUSTERID,
                       11,
                       strBuf,
                       &SampleApp_MsgID,
                       AF_DISCV_ROUTE,
                       AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
  {
  }
  else
  {
    // Error occurred in request to send.
  }   
}

//获取IEEE短地址
void GetIeeeAddr(uint8 * pIeeeAddr, uint8 *pStr)
{
  uint8 i;
  uint8 *xad = pIeeeAddr;

  for (i = 0; i < Z_EXTADDR_LEN*2; xad--)
  {
    uint8 ch;
    ch = (*xad >> 4) & 0x0F;
    *pStr++ = ch + (( ch < 10 ) ? '0' : '7');
    i++;
    ch = *xad & 0x0F;
    *pStr++ = ch + (( ch < 10 ) ? '0' : '7');
    i++;
  }
}

//校验码
uint8 XorCheckSum(uint8 * pBuf, uint8 len)
{
    uint8 i;
    uint8 byRet=0;

    if(len == 0)
        return byRet;
    else
        byRet = pBuf[0];

    for(i = 1; i < len; i ++)
        byRet = byRet ^ pBuf[i];

    return byRet;
}

//数据长度
uint8 GetDataLen(uint8 fc)
{
    uint8 len=0;
    switch(fc)
    {
    case 0x0A:
    case 0x0B:
    case 0x0C:
    case 0x0D:
      len = 1;
      break;
    case 0x02:
      len = 5;
      break;
    case 0x09:
      len = 6;
      break;
    }
    
    return len;
}

#if defined(ZDO_COORDINATOR)
#else
void iccardcode()
{
    unsigned char cmd;
    unsigned char status;

    cmd = RevBuffer[0];
    switch(cmd)
    {
    case 1:     // Halt the card     //终止卡的操作
        status= PcdHalt();
        RevBuffer[0]=1;
        RevBuffer[1]=status;
        break;
    case 2:     // Request,Anticoll,Select,return CardType(2 bytes)+CardSerialNo(4 bytes)
            // 寻卡，防冲突，选择卡    返回卡类型（2 bytes）+ 卡系列号(4 bytes)
        status= PcdRequest(RevBuffer[1],&RevBuffer[2]);
        if(status!=0)
        {
            status= PcdRequest(RevBuffer[1],&RevBuffer[2]);
            if(status!=0)
            {
            RevBuffer[0]=1; 
            RevBuffer[1]=status;
            break;
            }
        }  
        RevBuffer[0]=3; 
        RevBuffer[1]=status;
        break;

    case 3:                         // 防冲突 读卡的系列号 MLastSelectedSnr
        status = PcdAnticoll(&RevBuffer[2]);
        if(status!=0)
        {
            RevBuffer[0]=1; 
            RevBuffer[1]=status;
            break;
        }
        memcpy(MLastSelectedSnr,&RevBuffer[2],4);
        RevBuffer[0]=5;
        RevBuffer[1]=status;
        break;
    case 4:                   // 选择卡 Select Card
        status=PcdSelect(MLastSelectedSnr);
        if(status!=MI_OK)
        {
            RevBuffer[0]=1; 
            RevBuffer[1]=status;
            break;
        }
        RevBuffer[0]=3;
        RevBuffer[1]=status;
        break;
    case 5:     // Key loading into the MF RC500's EEPROM
        status = PcdAuthState(RevBuffer[1], RevBuffer[3], DefaultKey, MLastSelectedSnr);// 校验卡密码
        RevBuffer[0]=1;
        RevBuffer[1]=status;
        break;
    case 6: 
        RevBuffer[0]=1;
        RevBuffer[1]=status;
        break;
    case 7:     
        RevBuffer[0]=1;
        RevBuffer[1]=status;
        break;
    case 8:     // Read the mifare card
            // 读卡
        status=PcdRead(RevBuffer[1],&RevBuffer[2]);
        if(status==0)
        {RevBuffer[0]=17;}
        else
        {RevBuffer[0]=1;}
        RevBuffer[1]=status;            
        break;
    case 9:     // Write the mifare card
            // 写卡  下载密码
        status=PcdWrite(RevBuffer[1],&RevBuffer[2]);
        RevBuffer[0]=1;
        RevBuffer[1]=status;            
        break;
    case 10:
        PcdValue(RevBuffer[1],RevBuffer[2],&RevBuffer[3]);
        RevBuffer[0]=1; 
        RevBuffer[1]=status;
        break;
    case 12:    // 参数设置
        PcdBakValue(RevBuffer[1], RevBuffer[2]);
        RevBuffer[0]=1;//contact
        RevBuffer[1]=0;
        break;
    }
}
#endif


uint8 CheckSum(uint8 *pdata, uint8 len)
{
    uint8 i;
    uint8 check_sum=0;

    for(i=0; i<len; i++)
    {
        check_sum += pdata[i];
    }
    return check_sum;
}

//TODO::准备启用该代码
/**
*fc:功能码
*data:上传的数据
*len:数据长度
格式:len,校验,fc,内容,$,@,
*/

void packDataAndSend(uint8 fc, uint8* data, uint8 len)
{
    osal_memset(SampleApp_TxBuf, 0, SAMPLE_APP_TX_MAX+1);
    //数据包长度
    SampleApp_TxBuf[0]=3+len;
    //功能码
    SampleApp_TxBuf[2]=fc;
    //发送的数据
    if(len>0)
    {
        osal_memcpy(SampleApp_TxBuf+3, data, len);
    }
    //校验和,从fc开始，
    SampleApp_TxBuf[1]=CheckSum(SampleApp_TxBuf+2, len+1);
    //数据结尾
    SampleApp_TxBuf[3+len]='$';
    SampleApp_TxBuf[4+len]='@';
    //发送长度
    SampleApp_TxLen=5+len;
    //接着发数据包
    HalUARTWrite(0,SampleApp_TxBuf, SampleApp_TxLen);
}


//读取MQ2的浓度
uint8 GetMq2()
{
  uint16 adc= 0;
  float vol=0.0; //adc采样电压  
  uint8 percent=0;//百分比的整数值

  //读MQ2浓度
  adc= HalAdcRead(HAL_ADC_CHANNEL_6, HAL_ADC_RESOLUTION_14);

  //最大采样值8192(因为最高位是符号位)
  //2的13次方=8192
  if(adc>=8192)
  {
    return 0;
  }

  //转化为百分比
  vol=(float)((float)adc)/8192.0;
     
  //取百分比两位数字
  percent=(int)(vol*100);

  return percent;
}

void SetBuzzer(uint8 on)
{
  if(on>0)
  {
    P0_7=0;
  }
  else
  {
    P0_7=1;  
  }
}

void SetRelay(uint8 on)
{
  if(on>0)
  {
    P0_4=0;
  }
  else
  {
    P0_4=1;  
  }
}

//BCD转ASC码表
char NumberToLetter(unsigned char number)
{
    char buff[]="0123456789ABCDEF";
    if(number>15) return 0;
    return buff[number];

}


#if defined(ZDO_COORDINATOR)
void SampleApp_Check_Alive()
{
  uint8 i = 0;
  uint8 sum = 0;
  for(i = 0; i < MAX_NODE; i++)
  {
    if(Node_Check_Alive[i])
    {
      if(!Node_Alived[i])
      {
        Node_Alived[i] = 1;
        
        Uart_Buf[0] = COME_MSG;
        Uart_Buf[1] = 0x00;
        Uart_Buf[2] = i+1;
        Uart_Buf[3] = EP_COME;
        Uart_Buf[4] = XorCheckSum(Uart_Buf, 4);
        Uart_Buf[5] = MSG_END;
        HalUARTWrite (UART0, Uart_Buf, 6);
      }
      ++sum;
      Node_Check_Alive[i] = 0;
    }
    else
    {
      if(Node_Alived[i])
      {
        Uart_Buf[0] = COME_MSG;
        Uart_Buf[1] = 0x00;
        Uart_Buf[2] = i+1;
        Uart_Buf[3] = EP_LIVE;
        Uart_Buf[4] = XorCheckSum(Uart_Buf, 4);
        Uart_Buf[5] = MSG_END;
        HalUARTWrite (UART0, Uart_Buf, 6);
        Node_Alived[i] = 0;
      }
      
    }
  }
  if(sum != SampleApp_Connected)
  {
    SampleApp_Connected = sum;
    Lcd_New_Data = 1;
  }
}

void SampleApp_LCD_Display()
{
  //功能名称列表
  static uint8 Lcd_Page;                  //LCD页数
static char SampleApp_Function_Name[][11]={" 开启警报 ", " 关闭警报 ", "   监控   ", "   报警   ", "   主页   "};
static uint8 SampleApp_Function_Length = 5;
static uint8 SampleApp_Function_Index = 0; //当前选择的功能
static int SampleApp_Node_Index = 0;       //当前选择的终端号

  if(Lcd_New_Data)
  {
    if(SampleApp_State)
    {
      Lcd_Page = 2;
      SampleApp_Function_Index = 3;
      //SampleApp_Key_Pressed = 0;
    }
    if(SampleApp_Key_Pressed == 2)
    {
      if(Lcd_Page == 1)
      {
        SampleApp_Function_Index = (SampleApp_Function_Index+1)%SampleApp_Function_Length;
      }
      else if(Lcd_Page == 2 && SampleApp_Function_Index == 2)
      {
        SampleApp_Node_Index = (SampleApp_Node_Index+1)%MAX_NODE;
      }
      else if(Lcd_Page == 2 && SampleApp_Function_Index == 3)
      {
        SampleApp_SendDataToEndDevice(OPEN_ALARM, 7);
        SampleApp_Alarm_Switch = 1;
        SampleApp_State = 1;
      }
      SampleApp_Key_Pressed = 0;
    }
    else if(SampleApp_Key_Pressed == 1)
    {
      switch(Lcd_Page)
      {
      case 2:
        if(SampleApp_Function_Index == 3)
        {
          SampleApp_SendDataToEndDevice(CLOSE_ALARM, 7);
          SampleApp_Alarm_Switch = 0;
          SampleApp_State = 0;
          SampleApp_Alarm_Area = 0;
          Lcd_Page = 0;
          SampleApp_Function_Index = 0;
          SetBuzzer(0);
          break;
        }
        else
        {
          Lcd_Page = 1;
          break;
        }
      case 1:
      case 0:
        ++Lcd_Page;
        break;
      default:
        //++Lcd_Page;
        break;
      }
      SampleApp_Key_Pressed = 0;
    }
    
    
    switch(Lcd_Page)
    {
    case 0:
      Lcd_Update = 0;
      HalLcdWriteString( "    智云监控", HAL_LCD_LINE_1 );
      sprintf(Lcd_Buf, " 终端在线数: %d", SampleApp_Connected);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_2 );
      sprintf(Lcd_Buf, "    状态: %d", SampleApp_State);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_3 );
      if(Time_Sec/3600)
      {
        sprintf(Lcd_Buf, "    %02d : %02d", (int)(Time_Sec/3600), (int)((Time_Sec%3600)/60));
      }
      else
      {
        sprintf(Lcd_Buf, "    %02d : %02d", (int)(Time_Sec/60), (int)(Time_Sec%60));
      }
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_4 );
      Lcd_New_Data = 0;
      break;
    case 1:
      Lcd_Update = 0;
      HalLcdWriteString( "    功能选择", HAL_LCD_LINE_1 );
      sprintf(Lcd_Buf, "   %s", SampleApp_Function_Name[SampleApp_Function_Index-1 >= 0 ? SampleApp_Function_Index-1:SampleApp_Function_Length-1]);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_2 );
      sprintf(Lcd_Buf, ">  %s  <", SampleApp_Function_Name[SampleApp_Function_Index]);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_3 );
      sprintf(Lcd_Buf, "   %s", SampleApp_Function_Name[SampleApp_Function_Index+1 < SampleApp_Function_Length ? SampleApp_Function_Index+1:0]);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_4 );
      Lcd_New_Data = 0;
      break;
    case 2:
      sprintf(Lcd_Buf, ">  %s  <", SampleApp_Function_Name[SampleApp_Function_Index]);
      HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_1 );
      switch(SampleApp_Function_Index)
      {
      case 0:
        Lcd_Update = 0;
        SampleApp_SendDataToEndDevice(OPEN_ALARM, 7);
        SampleApp_Alarm_Switch = 1;
        HalLcdWriteString( "   按下S2重复", HAL_LCD_LINE_2 );
        HalLcdWriteString( "   按下S1返回", HAL_LCD_LINE_3 );
        HalLcdWriteString( "", HAL_LCD_LINE_4 );
        Lcd_New_Data = 0;
        break;
      case 1:
        Lcd_Update = 0;
        SampleApp_SendDataToEndDevice(CLOSE_ALARM, 7);
        SampleApp_Alarm_Switch = 0;
        HalLcdWriteString( "   按下S2重复", HAL_LCD_LINE_2 );
        HalLcdWriteString( "   按下S1返回", HAL_LCD_LINE_3 );
        HalLcdWriteString( "", HAL_LCD_LINE_4 );
        Lcd_New_Data = 0;
        break;
      case 3:
        Lcd_Update = 1;
        sprintf(Lcd_Buf, "  区域:%d", SampleApp_Alarm_Area);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_2 );
        sprintf(Lcd_Buf, "  温度:%.1f", Node_Data[SampleApp_Alarm_Area-1][0]+Node_Data[SampleApp_Alarm_Area-1][1]*0.1);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_3 );
        sprintf(Lcd_Buf, "  烟雾浓度:%d",  Node_Data[SampleApp_Alarm_Area-1][2]);
        //sprintf(Lcd_Buf, "  烟雾浓度:%d",  SampleApp_State);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_4 );
        
        Lcd_New_Data = 0;
        break;
      case 2:
        Lcd_Update = 1;
        sprintf(Lcd_Buf, "  温度:%.1f", Node_Data[SampleApp_Node_Index][0]+Node_Data[SampleApp_Node_Index][1]*0.1);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_2 );
        sprintf(Lcd_Buf, "  烟雾浓度:%d",  Node_Data[SampleApp_Node_Index][2]);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_3 );
        sprintf(Lcd_Buf, "  终端编号:%d",  SampleApp_Node_Index+1);
        HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_4 );
        Lcd_New_Data = 0;
        break;
      case 4:
        Lcd_Update = 0;
        Lcd_Page = 0;
        SampleApp_Function_Index = 0;
        HalLcdWriteString( "", HAL_LCD_LINE_2 );
        HalLcdWriteString( "", HAL_LCD_LINE_3 );
        HalLcdWriteString( "", HAL_LCD_LINE_4 );
        break;
      default:
        Lcd_Page = 0;
        break;
      }
      break;
    default:
      break;
    }
  }
  
  if(Lcd_Page == 0)
  {
    if(Time_Sec/3600)
    {
      sprintf(Lcd_Buf, "    %02d : %02d", (int)(Time_Sec/3600), (int)((Time_Sec%3600)/60));
    }
    else
    {
      sprintf(Lcd_Buf, "    %02d : %02d", (int)(Time_Sec/60), (int)(Time_Sec%60));
    }
    HalLcdWriteString( Lcd_Buf, HAL_LCD_LINE_4 );
  }
  
}

uint8 TxBuffer[128];
//查询终端数据
uint8 SendData(uint8 addr, uint8 FC)
{
    uint8 ret, i, index=4;

    TxBuffer[0] = 0x3A;
    TxBuffer[1] = 0x00;
    TxBuffer[2] = addr;
    TxBuffer[3] = FC;
        
        
        
    switch(FC)
    {
    case 0x01: //查询所有终端传感器的数据
        for (i=0; i<MAX_NODE; i++)
        {
            osal_memcpy(&TxBuffer[index], Node_Data[i], 5);
            index += 5;
        }
        TxBuffer[index] = XorCheckSum(TxBuffer, index);
        TxBuffer[index+1] = 0x23;
        
        HalUARTWrite(UART0, TxBuffer, index+2);
        ret = 1;
        break;
    case 0x04: //查询单个终端上所有传感器的数据
        if(addr == 0)
                {
                  TxBuffer[4] = SampleApp_Alarm_Switch;
                  TxBuffer[5] = SampleApp_Connected;
                  TxBuffer[6] = SampleApp_State;
                  TxBuffer[7] = SampleApp_Alarm_Area;
                  TxBuffer[8] = GetMq2();
                  TxBuffer[9] = XorCheckSum(TxBuffer, 9);
                  TxBuffer[10] = 0x23;
                  HalUARTWrite(UART0, TxBuffer, 11);
        ret = 1;
                  break;
                }
                osal_memcpy(&TxBuffer[index], Node_Data[addr-1], 5);
        index += 5;
        TxBuffer[index] = XorCheckSum(TxBuffer, index);
        TxBuffer[index+1] = 0x23; 
        HalUARTWrite(UART0, TxBuffer, index+2);
        ret = 1;
        break;
        case 0x03: //查询单个终端上RFID数据
                if(Card_Come[addr-1])
                {
                  osal_memcpy(&TxBuffer[index], Card_Buff[addr-1], 6);
                  Card_Come[addr-1] = 0;
                }
                else
                {
                  osal_memset(&TxBuffer[index], 0, 6);
                }
                index += 6;
                TxBuffer[index] = XorCheckSum(TxBuffer, index);
                TxBuffer[index+1] = 0x23; 
                HalUARTWrite(UART0, TxBuffer, index+2);
        ret = 1;
                break;
    default:
        ret = 0;
        break;
    }

    return ret;
}
#endif