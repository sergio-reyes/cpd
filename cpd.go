package cpd


import (
    "bufio" 
    "os"
    "strings"
    "encoding/csv"
    "strconv"
    "io"
    "fmt"
    "math"
    "math/rand"
    "sort"
)

// ///////////////////// CONSTANTS
const DEF_BOOTSTRAP=10000
const NO_TIME_COL  = 0	
const DEF_DATA_COL = 1
const DEF_MIN_CONF= 95
const MaxUint = ^uint(0)
const MinUint = 0
const MaxInt = int(MaxUint >> 1)
const MinInt = -MaxInt - 1
const DEF_MIN_INTERVAL = 1
const DEF_CHG_TOLERANCE = 10
const THETA_RANGE = 10
const DIST_SCORE_THRESH=5
const MATCH_THRESH=9


// ///////////////////// TYPES
type CoordT struct {
	X float64
	Y float64
}

type ChgT struct {
    Index int64
    Conf  float64
    Avg   float64
    Stdev float64
    ChgStartLine  int64
    ChgEndLine    int64
    ChgStartTime  string
    ChgEndTime    string
    ChgStartValue float64
    ChgEndValue   float64
    Subtle bool
    PrevChgIndex int64
} 

type RangeT struct{
    ID int64    `json:"id"`
    Start int64 `json:"start"`
    End int64   `json:"end"`
}

type PatternT struct{
    Avg   float64
    Stdev float64
    ChgSet []int64 
    RangeA []RangeT 
}

type RangeGroupT struct{
    PatternID int64 `json:"pattern_id"`
    Match bool      `json:"match"`
    RangeA []RangeT `json:"range"`
}

type ChgA  []ChgT 
type PatternA  []PatternT
type DataT []float64
type TimeT []string


// ///////////////////// GLOBALS
var G_chgA ChgA 
var G_matchA PatternA 
var G_chgAPost ChgA
var G_timeCol,G_dataCol int32
var G_delim rune
var G_rawData DataT
var G_timeData TimeT
var G_minConf float64
var G_bootstrap int64
var G_chgTolerance int
var G_matchStrList map[string]struct{}


//custom sorting functions
func (slice ChgA) Len() int {
    return len(slice)
}

func (slice ChgA) Less(i, j int) bool {
    return slice[i].Index < slice[j].Index;
}

func (slice ChgA) Swap(i, j int) {
    slice[i], slice[j] = slice[j], slice[i]
}


func calcAvg(data []float64)( float64){

	//-----------------------------------------------------------------------------------
	//  Simple average calculation.  
	//	Input:   array of floats
	//	Output:  float avg
	//-----------------------------------------------------------------------------------

        //variables
        var sum float64

        //init
        sum=0

        for _, value := range data {
                sum=sum+value
        }

        return(sum/((float64)(len(data))))
}

func calcStdev(data []float64, avg float64 )(float64){

	//-----------------------------------------------------------------------------------
	//  Calculates standard deviation      
	//	Input:  array of floats, pre-calculated average
	//	Output: stdev as float
	//-----------------------------------------------------------------------------------

        var sd float64

        for _, value := range data{
                sd += math.Pow(value - avg , 2)
        }

        sd = math.Sqrt(sd/float64(len(data)))

        return sd
}

func calcCusum(avg float64, data []float64) (float64, int64) {

	//-----------------------------------------------------------------------------------
	//  Calculates cusum, returning delta between max and min cusum values, along with 
	//  array index of max or min value
	//	Input:  avg, data to analyze
	//	Output: max/min delta, index of max or min
	//-----------------------------------------------------------------------------------

        //variables
        var cusumA []float64
        var maxC,minC float64
        var peakIndex int64
        var peak float64
        cusumA=append(cusumA,0.0)

        //init
        minC=(float64)(MaxInt)
        maxC=(float64)(MinInt)
        peak=0.0
        peakIndex=0

        //calculate the cusum, min and max diff
        for dataIndex := range data{
                cusumA=append(cusumA,cusumA[dataIndex]+(data[dataIndex]-avg))
                if (cusumA[dataIndex+1] > maxC){
                        maxC=cusumA[dataIndex+1]
                }
                if (cusumA[dataIndex+1] < minC){
                        minC=cusumA[dataIndex+1]
                }

                if (cusumA[dataIndex+1] > 0){
                        if (cusumA[dataIndex+1] > peak){
                                peak=cusumA[dataIndex+1]
                                peakIndex=int64(dataIndex)
                        }
                }else{
                        if ( (cusumA[dataIndex+1]*(-1)) > peak){
                                peak=cusumA[dataIndex+1]*(-1)
                                peakIndex=int64(dataIndex)
                        }
                }
        }

        return maxC-minC,peakIndex
}

func SetBootstrapLimit(bootstrap int64){

	//-----------------------------------------------------------------------------------
	//  Sets the bootstrap number; the limit at which a point is tested for a change
	//	Input:   bootstrap count
	//	Output:  
	//-----------------------------------------------------------------------------------

	G_bootstrap=bootstrap
}

func SetTimeCol(timeCol int32){

	//-----------------------------------------------------------------------------------
	//  Specifies which column of data contains time of day
	//	Input:   column number
	//	Output:  
	//-----------------------------------------------------------------------------------

	//if valid col:
	if (timeCol > 0){
		G_timeCol=timeCol
	}
}

func SetDataCol(dataCol int32){

	//-----------------------------------------------------------------------------------
	//  Updates global var to denote which col has the data
	//	Input:   column number
	//	Output:  
	//-----------------------------------------------------------------------------------

	//if valid col:
	if (dataCol > 0){
		G_dataCol=dataCol
	}
}

func SetTimeNDataCols(timeCol, dataCol int32) {

	//-----------------------------------------------------------------------------------
	//  Updates global var to denote which col has the data
	//	Input:   column number
	//	Output:  
	//-----------------------------------------------------------------------------------

	SetTimeCol(timeCol)
	SetDataCol(dataCol)
}

func SetChgTolerance(i int){

	//-----------------------------------------------------------------------------------
	//  Sets the change tolerance.  Not considered a change if < %tolerance.  Whole number
	//  percentage,  0-100
	//	Input:   column number
	//	Output:  
	//-----------------------------------------------------------------------------------

	G_chgTolerance=i
}

func NoTimeCol() {

	//-----------------------------------------------------------------------------------
	//  Flag that data file does not have a data column.  Output will be numbered instead
	//	Input:   
	//	Output:  
	//-----------------------------------------------------------------------------------

	G_timeCol=NO_TIME_COL
}


func SetDelim(delim rune){

	//-----------------------------------------------------------------------------------
	//  Specifies the delimiter in the data file
	//	Input:   
	//	Output:  
	//-----------------------------------------------------------------------------------

	G_delim=delim
}

func rollBackData( errCol int32, goodRow int64){

        //-----------------------------------------------------------------------------------
        //  If parsing or any other error found, delete data from global structs, preventing
	//  partial data entries
        //      Input:   column where error occured, row of last good data
        //      Output:  
        //-----------------------------------------------------------------------------------

	if (G_dataCol < errCol){
		G_rawData=append(DataT(nil), G_rawData[:goodRow]...)
	}

	if (G_timeCol < errCol){
		G_timeData=append(TimeT(nil), G_timeData[:goodRow]...)
	}

}

func _getDataFromFile(fname string, tCol, dCol int32) {

        //-----------------------------------------------------------------------------------
        //  Takes data from file and populates global structures
        //      Input:   filename, id for columns that have time stamps and data
        //      Output:  
        //-----------------------------------------------------------------------------------

	//var 
	var f float64
	var rowCount int64

        // Load file.
        file, _ := os.Open(fname)

        // Create a new reader.
        r := csv.NewReader(bufio.NewReader(file))

	//set the delimeter:
	r.Comma=G_delim

	rowCount=0
        for {
                record, err := r.Read()
                // Stop at EOF.
                if err == io.EOF {
                        break
                }

		if (len(record)>1){
                	for index := range record {

				//go to next record if already have all necessary data:
				if (  ( int32(index+1) > G_dataCol ) && ( int32(index+1) > G_timeCol) ){
					break;
				}

				//only count once per row
				if (index == 0){
					rowCount=rowCount+1

					//no time column
					if (G_timeCol==NO_TIME_COL){
						//use incremental values in place of time
                                       		strRCount:=fmt.Sprintf("%10d",rowCount)
                                       		G_timeData=append(G_timeData,strRCount)
					}

				}

				if (int32(index+1)==G_dataCol) {

					f, err = strconv.ParseFloat(strings.TrimSpace(record[index]),64)
					if (err == nil){
					
						G_rawData=append(G_rawData,f)


                        		}else{ //invalid record
						//last row does not count:
						rowCount=rowCount-1
				
						//roll back data stored in arrays	
						rollBackData(int32(index+1),rowCount)

						//stop processing record
						break;	
					}
				}

                                if (int32(index+1)==G_timeCol) {
					//use incremental values in place of time
                                       	G_timeData=append(G_timeData,record[index])
                                }
                	}
		}
        }
}

func GetDataFromFile(fname string){

        //-----------------------------------------------------------------------------------
        //  Takes data from file and populates global structures
        //      Input:   filename
        //      Output:  
        //-----------------------------------------------------------------------------------
	
	_getDataFromFile(fname,G_timeCol,G_dataCol)
}


func findChange(lookRight bool, base_start, base_end, chgPt int64, origData []float64){

        //-----------------------------------------------------------------------------------
        //  Recursive function that does the change point analysis. Continues while there are
	//  segments of the array to be analyzed 
        //      Input:   direction to look (left/right), start_index, stop_index, 
	//			last_chgpt, data array
        //      Output:  
        //-----------------------------------------------------------------------------------


	//var
        var slice []float64
        var newDelta float64
        var origDelta float64
        var oneChg ChgT
	var lookLeft bool

	//init - can only look left or right:
	lookLeft=false
	if lookRight == false{
		lookLeft=true
	}
	
        //if data requires inspection:
        if (chgPt > int64(0) && lookLeft==true) || (chgPt<int64(len(origData)) && lookRight==true) {

                //get slice of data that is to be operated on:
                if (lookLeft){
                        slice=origData[:chgPt]
                        base_end=base_start+chgPt-1
                        base_start=base_end-int64(len(slice))+1
                }else{
                        slice=origData[chgPt:]
                        base_start=base_start+chgPt
                        base_end=base_start+int64(len(slice)-1)
                }


                	//get a copy of the data
                	bootstrap := make([]float64, len(slice), (cap(slice)))

                	//copy contents over
                	copy(bootstrap,slice)

                	//calculate the average
                	avg:=calcAvg(slice)

                	//gather original-ordered data cusum
                	origDelta,chgPt=calcCusum(avg, slice)

                	gtCount:=0
                	//bootstrap to detect confidence in change
                	for bootIndex := int64(0); bootIndex < G_bootstrap; bootIndex++ {
				//random sort the data in slice
                        	for i := range bootstrap{
                                	j := rand.Intn(i + 1)
                                	bootstrap[i], bootstrap[j] = bootstrap[j], bootstrap[i]
                        	}
				//get cusum of random ordered data
                        	newDelta,_=calcCusum(avg, bootstrap)

                        	if (origDelta > newDelta){
                                	gtCount=gtCount+1
                        	}
                	}

                	//calculate change confidence:
                	conf:=float64(100*(float64(gtCount)/float64(G_bootstrap)))

                	if (conf >= G_minConf){

                        	//save off change s
                        	oneChg.Index=chgPt+1+base_start
                        	oneChg.Conf=conf
                        	G_chgA=append(G_chgA,oneChg)

                        	newOrig := make([]float64, len(slice), (cap(slice)))
                        	copy(newOrig,slice)

				//look left
                        	findChange(false,base_start,base_end,chgPt+1,newOrig)

				//look right
                        	findChange(true, base_start,base_end,chgPt+1,newOrig)
                	}

        }
}

func pass1PostProc(){

        //-----------------------------------------------------------------------------------
        //  Go through all changes, calculating a summary of the change itself, avg, linenum
	//  flag if any changes are to  "subtle" (aka < user_specified_chgTolerance)
        //      Input:   works off global structs
        //      Output:  
        //-----------------------------------------------------------------------------------

	var slice[]float64
	var delta float64
	var dindex int64

        //summarize the changes by updating their records
        for i := 0; i < (len(G_chgA)-1); i++ {

		//init
                G_chgA[i].PrevChgIndex=0

                //performance
                slice=G_rawData[G_chgA[i].Index:G_chgA[i+1].Index]
                G_chgA[i].Avg=calcAvg(slice)
                G_chgA[i].Stdev=calcStdev(slice,G_chgA[i].Avg)

                //line numbers
		G_chgA[i].ChgStartLine=G_chgA[i].Index+1
		G_chgA[i].ChgEndLine=G_chgA[i+1].Index

                //time
		G_chgA[i].ChgStartTime=G_timeData[G_chgA[i].Index]
		G_chgA[i].ChgEndTime=G_timeData[G_chgA[i+1].Index-1]

                //value
		G_chgA[i].ChgStartValue=G_rawData[G_chgA[i].Index]
		G_chgA[i].ChgEndValue=G_rawData[G_chgA[i+1].Index-1]

		//check if change is too subtle
		if (i > 0){

			//avoid regression creep, find parent change:
			if (G_chgA[i-1].PrevChgIndex == 0){
				dindex=int64(i-1)
			}else{
				dindex=G_chgA[i-1].PrevChgIndex
			}

			//calculate delta
			delta=(G_chgA[i].Avg/G_chgA[dindex].Avg)	
			if (G_chgA[i].Avg < G_chgA[dindex].Avg){
				delta=(G_chgA[i].Avg/G_chgA[dindex].Avg)	
			}else{
				delta=(G_chgA[dindex].Avg/G_chgA[i].Avg)	
			}
			delta=math.Abs(100-((delta*100)+0.5))

			//if not enough a change:
			if (int(delta) <= G_chgTolerance) {
				G_chgA[i].Subtle=true	
				G_chgA[i].PrevChgIndex=dindex
			}
		}
        }

}

func pass2PostProc(){

        //-----------------------------------------------------------------------------------
        //  Go through all changes, merging subtle changes with obvious changes and 
	//  summarizing the changes
        //      Input:   
        //      Output:  
        //-----------------------------------------------------------------------------------

        var slice[]float64
	var pindex,sindex int64
	var oneChg ChgT

	//init
	pindex=-1

        //copy over and re-calculate the final chgA
        for i := 0; i < (len(G_chgA)-1); i++ {

		//don't process subtle changes
		if (!G_chgA[i].Subtle){
	
			G_chgAPost=append(G_chgAPost,oneChg)
			pindex=pindex+1

			//look forward until all subtle changes are merged:
			sindex=int64(i+1)
			for ; G_chgA[sindex].Subtle && (sindex<int64(len(G_chgA)-1)); sindex++ {}

			
                	//performance
                	slice=G_rawData[G_chgA[i].Index:G_chgA[sindex].Index]
                	G_chgAPost[pindex].Avg=calcAvg(slice)
                	G_chgAPost[pindex].Stdev=calcStdev(slice,G_chgAPost[pindex].Avg)

                	//line numbers
                	G_chgAPost[pindex].ChgStartLine=G_chgA[i].Index+1
                	G_chgAPost[pindex].ChgEndLine=G_chgA[sindex].Index

                	//time
                	G_chgAPost[pindex].ChgStartTime=G_timeData[G_chgA[i].Index]
                	G_chgAPost[pindex].ChgEndTime=G_timeData[G_chgA[sindex].Index-1]

                	//value
                	G_chgAPost[pindex].ChgStartValue=G_rawData[G_chgA[i].Index]
                	G_chgAPost[pindex].ChgEndValue=G_rawData[G_chgA[sindex].Index-1]

                	//conf
                	G_chgAPost[pindex].Conf=G_chgA[i].Conf
		}
        }
}

func FindChange(){

	//-----------------------------------------------------------------------------------
	//  Finds the changes in data, stores them in a struct, then calls other functions
	//  to summarize the changes found. 	 
	//	Input:   
	//	Output:  update change struct
	//-----------------------------------------------------------------------------------

        var oneChg ChgT

        //init for change detection
        chgPt:=int64(len(G_rawData))
	if (chgPt > 0){

		G_chgA=G_chgA[:0]

        	//load init changes (beginning and dummy_end)
        	oneChg.Index=0 
		oneChg.Conf=0
        	G_chgA=append(G_chgA,oneChg)

		//dummy data point at length_of_data_+1
        	oneChg.Index=int64(len(G_rawData))
        	oneChg.Conf=0
        	G_chgA=append(G_chgA,oneChg)

        	findChange(false,0,int64(len(G_rawData)-1),chgPt,G_rawData)

        	//sort change points by index
        	sort.Sort(G_chgA)

		//populate struct, flagging subtle changes
		pass1PostProc()

		//populate struct summarizing changes that occured
		pass2PostProc()

		//remove dummy change (last change point at len_of_data+1)
		G_chgA=G_chgA[:len(G_chgA)-1]
	}
}

func GetAllChanges()([]ChgT){

	//-----------------------------------------------------------------------------------
	//  Returns the structure containing information of all the detected changes
	//	Input:   
	//	Output:  array of structs describing changes
	//-----------------------------------------------------------------------------------

	return G_chgA
}

func GetChgDataVal(chgIndex int64)(DataT){

	//-----------------------------------------------------------------------------------
	//  Returns the data value at index
	//	Input:   index 
	//	Output:  raw data value
	//-----------------------------------------------------------------------------------

	var subset DataT

	if (chgIndex>=0) && (chgIndex<int64(len(G_chgA))){
		subset=G_rawData[(G_chgA[chgIndex].ChgStartLine-1):G_chgA[chgIndex].ChgEndLine]
		return subset
	}

	return subset
}

func GetChgTimeVal(chgIndex int64)(TimeT){

	//-----------------------------------------------------------------------------------
	//  Returns the time value at index
	//	Input:   index 
	//	Output:  raw time value
	//-----------------------------------------------------------------------------------

	var subset TimeT

	if (chgIndex>=0) && (chgIndex<int64(len(G_chgA))){
		subset=G_timeData[(G_chgA[chgIndex].ChgStartLine-1):G_chgA[chgIndex].ChgEndLine]
		return subset
	}

	return subset
}

func GetChgCount()(int){

	//-----------------------------------------------------------------------------------
	//  Find the number of changes found 
	//	Input:   
	//	Output:  number of change detected
	//-----------------------------------------------------------------------------------

	return len(G_chgA)
}

func _printChg(i int, indent bool){

	//-----------------------------------------------------------------------------------
	//  Prints a change given an index
	//	Input:   Change index, bool to determine if each line to be indented
	//	Output:  Output describing a change
	//-----------------------------------------------------------------------------------

	lineStr:="" 

	if G_timeCol==NO_TIME_COL{
		lineStr=fmt.Sprintf("Line Num: %04d -> %04d",G_chgAPost[i].ChgStartLine, G_chgAPost[i].ChgEndLine)
	}else{
		lineStr=fmt.Sprintf("Time: %v -> %v", G_chgA[i].ChgStartTime,G_chgA[i].ChgEndTime)
	}


	indentStr:="     "

	fmt.Printf("%sChg:%04d  ,  %s  len=%04d  ,  Avg:%#.2f, Stdev:%#.2f  ,  Chg. Conf %5.1f%% @: %d\n",
			indentStr,i,
                        lineStr, G_chgAPost[i].ChgEndLine-G_chgAPost[i].ChgStartLine+1,
                        G_chgAPost[i].Avg,G_chgAPost[i].Stdev,G_chgAPost[i].Conf,G_chgAPost[i].ChgStartLine)
}

func PrintChg(){

	//-----------------------------------------------------------------------------------
	//  Prints all changes
	//	Input:   
	//	Output:  Output describing all changes
	//-----------------------------------------------------------------------------------

        fmt.Println()
        fmt.Printf("Changes Found: %v\n",len(G_chgA))
        for i := 0; i < (len(G_chgAPost)); i++ {
		_printChg(i,false)
        }

        fmt.Println()
}

func PrintDebug(){

	//-----------------------------------------------------------------------------------
	//  Print all changes along with debug info concerning the changes
	//	Input:   
	//	Output:  
	//-----------------------------------------------------------------------------------

        fmt.Println()
        fmt.Printf("Changes Found: %v\n",len(G_chgA))
        for i := 0; i < (len(G_chgA)); i++ {

                fmt.Printf("Line Num: %10d -> %-10d  len=%-5d    [ Time: %v , Value: %10.3f ] -> [ Time: %v , Value: %10.3f ]  ,  Avg:%#.2f Stdev:%#.2f    %5.1f%% CONF. @: %d  Merge=%v\n",
			G_chgA[i].ChgStartLine, G_chgA[i].ChgEndLine, G_chgA[i].ChgEndLine-G_chgA[i].ChgStartLine+1,
                        G_chgA[i].ChgStartTime,G_chgA[i].ChgStartValue,G_chgA[i].ChgEndTime,G_chgA[i].ChgEndValue, 
                        G_chgA[i].Avg,G_chgA[i].Stdev,G_chgA[i].Conf,G_chgA[i].ChgStartLine,
			G_chgA[i].Subtle)

        }

        fmt.Println()

}

func init(){

	//-----------------------------------------------------------------------------------
	//  Initialization of data structures and values
	//	Input:   
	//	Output:  
	//-----------------------------------------------------------------------------------

	G_delim=','
	G_timeCol=NO_TIME_COL
	G_dataCol=DEF_DATA_COL
	G_minConf=DEF_MIN_CONF
	G_bootstrap=DEF_BOOTSTRAP
	G_chgTolerance=DEF_CHG_TOLERANCE
	G_matchStrList = make(map[string]struct{})
}

