// SPDX-License-Identifier: GPL-3.0
/*
    Copyright 2021 0KIMS association.

    This file is generated with [snarkJS](https://github.com/iden3/snarkjs).

    snarkJS is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    snarkJS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with snarkJS. If not, see <https://www.gnu.org/licenses/>.
*/

pragma solidity >=0.7.0 <0.9.0;

contract Groth16Verifier {
    // Scalar field size
    uint256 constant r    = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Base field size
    uint256 constant q   = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // Verification Key data
    uint256 constant alphax  = 20491192805390485299153009773594534940189261866228447918068658471970481763042;
    uint256 constant alphay  = 9383485363053290200918347156157836566562967994039712273449902621266178545958;
    uint256 constant betax1  = 4252822878758300859123897981450591353533073413197771768651442665752259397132;
    uint256 constant betax2  = 6375614351688725206403948262868962793625744043794305715222011528459656738731;
    uint256 constant betay1  = 21847035105528745403288232691147584728191162732299865338377159692350059136679;
    uint256 constant betay2  = 10505242626370262277552901082094356697409835680220590971873171140371331206856;
    uint256 constant gammax1 = 11559732032986387107991004021392285783925812861821192530917403151452391805634;
    uint256 constant gammax2 = 10857046999023057135944570762232829481370756359578518086990519993285655852781;
    uint256 constant gammay1 = 4082367875863433681332203403145435568316851327593401208105741076214120093531;
    uint256 constant gammay2 = 8495653923123431417604973247489272438418190587263600148770280649306958101930;
    uint256 constant deltax1 = 11559732032986387107991004021392285783925812861821192530917403151452391805634;
    uint256 constant deltax2 = 10857046999023057135944570762232829481370756359578518086990519993285655852781;
    uint256 constant deltay1 = 4082367875863433681332203403145435568316851327593401208105741076214120093531;
    uint256 constant deltay2 = 8495653923123431417604973247489272438418190587263600148770280649306958101930;

    
    uint256 constant IC0x = 6766476906838667366475121311965604272106955106792507001172450377471704802855;
    uint256 constant IC0y = 16625487059456204284677209819380242842829531439828465992356359770941034129061;
    
    uint256 constant IC1x = 9813725314302140905362027827467057995838189612051158392799252230227250509386;
    uint256 constant IC1y = 21500964453023295626687811502160960819576009508554341213079084800983713971924;
    
    uint256 constant IC2x = 18425399692765790282816017729717589067574104744020573373679619539385151370323;
    uint256 constant IC2y = 16064356854112574200509067847921558679594984785680442675526255205539019203120;
    
    uint256 constant IC3x = 3630585874370305870463047180209108603713871148071377209392452742432872021551;
    uint256 constant IC3y = 5467997654939774889089385427143337375172542680274287046226270083596217751142;
    
    uint256 constant IC4x = 2604898630830650493348276452406173340666266900720690750643751889228377554525;
    uint256 constant IC4y = 9284008177232642302927379613617185976971645903062909411509572819729566462988;
    
    uint256 constant IC5x = 10111292499343547104438228587585923689963236331154435529258340812529726325867;
    uint256 constant IC5y = 12544807093136807850604413087189496590410054929425778339957164292149717615641;
    
    uint256 constant IC6x = 6711644694278208928461868887266026977399286372843496048294089840044176848087;
    uint256 constant IC6y = 8004507553747366886113853287607355546362556757993969166022890386017983610891;
    
    uint256 constant IC7x = 12499079962155795932860161717617123900769212390303572438932536115199927573964;
    uint256 constant IC7y = 21440536128129717782551389577153012231724027261722125593357961818788469571364;
    
    uint256 constant IC8x = 12176612856365021722333011744746606375928062952147123934227769218585808601720;
    uint256 constant IC8y = 14140599925984909904632916871997788798740507363835911055896138485797569243974;
    
    uint256 constant IC9x = 7606189807039741475134684659023637378201980984404543956886917607913762554035;
    uint256 constant IC9y = 8842944097814309201996369561609163949803756686718329246581473349453078382970;
    
    uint256 constant IC10x = 4816463601836898807660314644315204022876557843630177701059529016081638733898;
    uint256 constant IC10y = 1666524201487500840045901823169842814741242514585471847765691410051828275253;
    
    uint256 constant IC11x = 17861220342952751877019108907012677875773759171906449036040318473945547798848;
    uint256 constant IC11y = 1064329541028991800288474301465255449866425915071592508456176933559411061798;
    
    uint256 constant IC12x = 18007919219688228643456746385998137575273433754742909149420774114729765751121;
    uint256 constant IC12y = 4696203914038026215908319339894345705292012857416779882056538935252943405184;
    
    uint256 constant IC13x = 9148673955311854757891858362898379534330452307968849897202196263076289204193;
    uint256 constant IC13y = 15776527321812431478031493454157124555526301721039292728660342547672455245071;
    
    uint256 constant IC14x = 1163657698609668076583892706567352274144823633750730620197392086727661699101;
    uint256 constant IC14y = 306208385886776289867533544047365885153185074041554206021487499725270580495;
    
    uint256 constant IC15x = 3997342354353902408199652460344258205174646786649950478989100942748903212586;
    uint256 constant IC15y = 2887955830588667366114833771344931212179996341147858238606851894819718309253;
    
    uint256 constant IC16x = 15688464885723248717281224393398213157511269959964706063892348650259615885745;
    uint256 constant IC16y = 965510045288364609041140576162992441436879132985254982286720615163744666655;
    
    uint256 constant IC17x = 4338774752730717011908756171764297516936100710972007864451647813349940993204;
    uint256 constant IC17y = 9872516481601419158254461122326766158013473488677475578547137009414522162565;
    
    uint256 constant IC18x = 1842086421830959338259561460559053898739856065437641237338716020481442466895;
    uint256 constant IC18y = 7250006312086298729036905454010447778366420804039582561522915712384993053131;
    
    uint256 constant IC19x = 18448134275313625203047294745393620415076492320860498345046256376839426682562;
    uint256 constant IC19y = 14206101573974579524688707991775856806488918975380344373062482974918356984713;
    
    uint256 constant IC20x = 3089107644075069317018575190665693650582150960980884201697709887809767553575;
    uint256 constant IC20y = 6860903579348917512207146061127645647532086082091084338923187927297268794467;
    
    uint256 constant IC21x = 17171854512390169530870406071077787005323563225022526503287000653833488732647;
    uint256 constant IC21y = 19726231277365272858907355701680023043869701462757785939560364794621939675398;
    
    uint256 constant IC22x = 6850545666127026326913126777586030099758383444728698651989785399615629499874;
    uint256 constant IC22y = 7334974045709724275855928652726965654723458430644535668322330480228570275578;
    
    uint256 constant IC23x = 13367102622771933459111638279758433472739874194460427889810473231563938560015;
    uint256 constant IC23y = 19403005927811582530087297123819678333954983632220525027972725656890167063022;
    
    uint256 constant IC24x = 1838779788574162939160680215010924490279385717423956825381421143708487086865;
    uint256 constant IC24y = 15238312351886103324528377109178013544291067703071125153020106662297084102640;
    
    uint256 constant IC25x = 8483298089090663554166668543255504726830503736594138426197221755647956797316;
    uint256 constant IC25y = 21781333768797642461614512666391466064061778999437513008928392744426564909664;
    
    uint256 constant IC26x = 21327454266861465316559084026373343585528595645777104202290367921100909848541;
    uint256 constant IC26y = 3030683124837254818492688796373565465043493485070515569489797681727986831303;
    
    uint256 constant IC27x = 12521844537530891904804723030977871479088405327179050360814526845625566865263;
    uint256 constant IC27y = 9631391258719462142211328852576766776846745963519877631405178126686852628493;
    
    uint256 constant IC28x = 18253979928758822877111222659853230430833235320727617524133765015401633776329;
    uint256 constant IC28y = 18954530742863585854858335554315097186893699760415925459511119766266094675966;
    
    uint256 constant IC29x = 5030779690520417482825988725869129325061202301968035890967983848407511320999;
    uint256 constant IC29y = 15346830494726495704331422143105346888736871453605262580899760792174060138758;
    
    uint256 constant IC30x = 1122048570327240450058528323705128866225436365382217821002668944591046395729;
    uint256 constant IC30y = 15478279000205279316965208565012079220638581690451601854099703236032375223127;
    
    uint256 constant IC31x = 15750900263862574408744393630861312605382593831815847835114833946455619441127;
    uint256 constant IC31y = 11720007096744577488627625272841528612028370436110733475658288267553121080948;
    
    uint256 constant IC32x = 5957116428785473021788755589774484757744582294594880799417167114985505813437;
    uint256 constant IC32y = 9607214418340590186354540938654210395391440688114260003875487848567985971591;
    
    uint256 constant IC33x = 1801281686921883163468728573514731722019440087619166793320297607910830925741;
    uint256 constant IC33y = 15320274032028200491361852700492775792643760654409488174236699682516439718197;
    
    uint256 constant IC34x = 1481933440410561191406744195363029824687210517300824407479550964832120760742;
    uint256 constant IC34y = 4834038605898908866146692723594071559182037921304097123270602717358886272620;
    
    uint256 constant IC35x = 16394283713416789773308360990114732882418048417420675141319146413327428620646;
    uint256 constant IC35y = 17697567944456786681344067641452284026315598770932434868726621012677287569443;
    
    uint256 constant IC36x = 11999886996329570254812750211497898904749550902519615578532839545156902198996;
    uint256 constant IC36y = 19820200359715857086229730835109214352572630444282027778256853040029691105481;
    
    uint256 constant IC37x = 11869390690582767044110954000477274190104588741563508585116882661764387452495;
    uint256 constant IC37y = 11360414933074467049900884962038461380281922172119454751493063633276874603492;
    
    uint256 constant IC38x = 14691122628185689791456614801473234598634592547125966582858063627046754118187;
    uint256 constant IC38y = 14446582241534180521866236893565583901880855923979125775724133105960782402614;
    
    uint256 constant IC39x = 18853417819115604825651842624905982406816645421312512465398122364230158983924;
    uint256 constant IC39y = 5143618764414393458875209824727071054206507952783554982819465898582669893251;
    
    uint256 constant IC40x = 13947094802370617139629481336909072710905348287424938841466977367631868377067;
    uint256 constant IC40y = 18546708660373268393163609784613222678737602880463938590980584649960782156208;
    
    uint256 constant IC41x = 9138926304057456796651576309609286606012293361067183900556573664710514873279;
    uint256 constant IC41y = 5795729169970533820523472988641747436864938239321075481628582076324201824488;
    
    uint256 constant IC42x = 13081717412920683873067941315281693763121470069810811375204803903453428582589;
    uint256 constant IC42y = 427274101038660797555353249879022673162927000767801441126079053427719194387;
    
    uint256 constant IC43x = 20425843361005758936821185261293320535725505644492276875750798744949825152423;
    uint256 constant IC43y = 13758374982194406081149652322066365379256361779937755676926450469692268795360;
    
    uint256 constant IC44x = 7845053400782127512903247566319557639196003523004489186027637413036644595638;
    uint256 constant IC44y = 13379430117365777581511969226351095766019429736105624143515916992539626881111;
    
    uint256 constant IC45x = 18065780194004982700033036077340018335006681342367149207616760604719296711572;
    uint256 constant IC45y = 16048119881390694430603749706801845546072833824853734558225509112647970832988;
    
    uint256 constant IC46x = 12141324517113273288184615743451307949581832829531571457391649074158644253805;
    uint256 constant IC46y = 20257560239707884920072940839434773460852233495185527441467954346978270618098;
    
    uint256 constant IC47x = 15149186890050285712483356635986777957572712778564376945830478875155314824320;
    uint256 constant IC47y = 13921148952686904889073233389631510734249142397124883173164645603930518205389;
    
    uint256 constant IC48x = 2950904376213532213991426817605948234705281094847280167584476660666934772374;
    uint256 constant IC48y = 15198177215356769923978580275185924758965431630851233210346569260196981976970;
    
    uint256 constant IC49x = 1555485420161289620075405514478784630533138905656871847439916299209734799041;
    uint256 constant IC49y = 4712386934057225456358776602470183936545795416944740133954025683225940245076;
    
    uint256 constant IC50x = 14380630647208495444998149472253303570094153280081638331388859204109228001963;
    uint256 constant IC50y = 12532778666773653509601435837979192083116325739321399542448838219445011194347;
    
    uint256 constant IC51x = 4218799003837859916858561091258180635677373196517625487465300845533189806837;
    uint256 constant IC51y = 12973985350502691480285344335927236738203635690446995759138302455427580237132;
    
    uint256 constant IC52x = 2723044792542400715997031945249758297680680293993868731070499640120794211363;
    uint256 constant IC52y = 20631938614019969588226678930601075285754127677193920651207916578590190402613;
    
    uint256 constant IC53x = 4746758466838825910964295396744638167725420299710093639904142500482119445132;
    uint256 constant IC53y = 9577156862490589665241191041765474700462125300407411384863870344041838563474;
    
    uint256 constant IC54x = 12686915810038058088775811562982058868789247698969107852243303259332198203738;
    uint256 constant IC54y = 3190232149273929994174541057158846481464522351080776989406582314605050148514;
    
    uint256 constant IC55x = 15265524831755639890101069830545497599812680174774902098634333965467909921110;
    uint256 constant IC55y = 13853464928907140489304023333113518676513681166154005741145535248250624612301;
    
    uint256 constant IC56x = 3571520333281213776747448370480706359415894865361100040030537924802531215532;
    uint256 constant IC56y = 15404177608872190617912768620591448073108533800611207502304271500457019492341;
    
    uint256 constant IC57x = 11811344394475781358402743104444173257387800109203306569490307092375525423463;
    uint256 constant IC57y = 13461609843953386758593753396111221724992738966357402103961121128234241297126;
    
    uint256 constant IC58x = 16329715410253664215203013752203481750976958212300436012444606432692768387856;
    uint256 constant IC58y = 9020518050207423016093240299241002602274936960096981575913540762100478240053;
    
    uint256 constant IC59x = 20627294386809383236188551388678795171286891797324328646753105618055798302954;
    uint256 constant IC59y = 14798064444078379155011823748812291754304484646378157002038910244379995899254;
    
    uint256 constant IC60x = 577541506168771259166957139835154516270600233267277083443131411966196853992;
    uint256 constant IC60y = 177017793560534528112600944855464687487630124448334631721120234591585115916;
    
    uint256 constant IC61x = 10511378844589991981049228641106062919725223724611591279516295464307859929904;
    uint256 constant IC61y = 16153919876753505909651436569198846232627433986050234118944300138100516584397;
    
    uint256 constant IC62x = 46259810854318551299883264625138598097330604739295307346296249033306200716;
    uint256 constant IC62y = 1836132873928253470945039897346518680392752020012198302486223530976364494020;
    
    uint256 constant IC63x = 17728093560531572245862967455371778336416473842487533035442373081508454252692;
    uint256 constant IC63y = 9846830885988869728962536899094836969841213682477524783384232585662077425950;
    
    uint256 constant IC64x = 19526930472877165539152009277921376048515378863184072024605911361452037738600;
    uint256 constant IC64y = 2459375398486908493442460254024080155448636269245133307543516500647062069446;
    
    uint256 constant IC65x = 16846478097328854570677825925915906438760852591456676423163921372722662347664;
    uint256 constant IC65y = 16207126545541112255696859221272078917789803910512534175101886002844509239689;
    
    uint256 constant IC66x = 13897892385615893712482369259643070654839870979920289818996194894999889456762;
    uint256 constant IC66y = 10730327254910684497868218035990270808131290472028199765377249148948022441473;
    
 
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[66] calldata _pubSignals) public view returns (bool) {
        assembly {
            function checkField(v) {
                if iszero(lt(v, r)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }
            
            // G1 function to multiply a G1 value(x,y) to value in an address
            function g1_mulAccC(pR, x, y, s) {
                let success
                let mIn := mload(0x40)
                mstore(mIn, x)
                mstore(add(mIn, 32), y)
                mstore(add(mIn, 64), s)

                success := staticcall(sub(gas(), 2000), 7, mIn, 96, mIn, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }

                mstore(add(mIn, 64), mload(pR))
                mstore(add(mIn, 96), mload(add(pR, 32)))

                success := staticcall(sub(gas(), 2000), 6, mIn, 128, pR, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            function checkPairing(pA, pB, pC, pubSignals, pMem) -> isOk {
                let _pPairing := add(pMem, pPairing)
                let _pVk := add(pMem, pVk)

                mstore(_pVk, IC0x)
                mstore(add(_pVk, 32), IC0y)

                // Compute the linear combination vk_x
                
                g1_mulAccC(_pVk, IC1x, IC1y, calldataload(add(pubSignals, 0)))
                
                g1_mulAccC(_pVk, IC2x, IC2y, calldataload(add(pubSignals, 32)))
                
                g1_mulAccC(_pVk, IC3x, IC3y, calldataload(add(pubSignals, 64)))
                
                g1_mulAccC(_pVk, IC4x, IC4y, calldataload(add(pubSignals, 96)))
                
                g1_mulAccC(_pVk, IC5x, IC5y, calldataload(add(pubSignals, 128)))
                
                g1_mulAccC(_pVk, IC6x, IC6y, calldataload(add(pubSignals, 160)))
                
                g1_mulAccC(_pVk, IC7x, IC7y, calldataload(add(pubSignals, 192)))
                
                g1_mulAccC(_pVk, IC8x, IC8y, calldataload(add(pubSignals, 224)))
                
                g1_mulAccC(_pVk, IC9x, IC9y, calldataload(add(pubSignals, 256)))
                
                g1_mulAccC(_pVk, IC10x, IC10y, calldataload(add(pubSignals, 288)))
                
                g1_mulAccC(_pVk, IC11x, IC11y, calldataload(add(pubSignals, 320)))
                
                g1_mulAccC(_pVk, IC12x, IC12y, calldataload(add(pubSignals, 352)))
                
                g1_mulAccC(_pVk, IC13x, IC13y, calldataload(add(pubSignals, 384)))
                
                g1_mulAccC(_pVk, IC14x, IC14y, calldataload(add(pubSignals, 416)))
                
                g1_mulAccC(_pVk, IC15x, IC15y, calldataload(add(pubSignals, 448)))
                
                g1_mulAccC(_pVk, IC16x, IC16y, calldataload(add(pubSignals, 480)))
                
                g1_mulAccC(_pVk, IC17x, IC17y, calldataload(add(pubSignals, 512)))
                
                g1_mulAccC(_pVk, IC18x, IC18y, calldataload(add(pubSignals, 544)))
                
                g1_mulAccC(_pVk, IC19x, IC19y, calldataload(add(pubSignals, 576)))
                
                g1_mulAccC(_pVk, IC20x, IC20y, calldataload(add(pubSignals, 608)))
                
                g1_mulAccC(_pVk, IC21x, IC21y, calldataload(add(pubSignals, 640)))
                
                g1_mulAccC(_pVk, IC22x, IC22y, calldataload(add(pubSignals, 672)))
                
                g1_mulAccC(_pVk, IC23x, IC23y, calldataload(add(pubSignals, 704)))
                
                g1_mulAccC(_pVk, IC24x, IC24y, calldataload(add(pubSignals, 736)))
                
                g1_mulAccC(_pVk, IC25x, IC25y, calldataload(add(pubSignals, 768)))
                
                g1_mulAccC(_pVk, IC26x, IC26y, calldataload(add(pubSignals, 800)))
                
                g1_mulAccC(_pVk, IC27x, IC27y, calldataload(add(pubSignals, 832)))
                
                g1_mulAccC(_pVk, IC28x, IC28y, calldataload(add(pubSignals, 864)))
                
                g1_mulAccC(_pVk, IC29x, IC29y, calldataload(add(pubSignals, 896)))
                
                g1_mulAccC(_pVk, IC30x, IC30y, calldataload(add(pubSignals, 928)))
                
                g1_mulAccC(_pVk, IC31x, IC31y, calldataload(add(pubSignals, 960)))
                
                g1_mulAccC(_pVk, IC32x, IC32y, calldataload(add(pubSignals, 992)))
                
                g1_mulAccC(_pVk, IC33x, IC33y, calldataload(add(pubSignals, 1024)))
                
                g1_mulAccC(_pVk, IC34x, IC34y, calldataload(add(pubSignals, 1056)))
                
                g1_mulAccC(_pVk, IC35x, IC35y, calldataload(add(pubSignals, 1088)))
                
                g1_mulAccC(_pVk, IC36x, IC36y, calldataload(add(pubSignals, 1120)))
                
                g1_mulAccC(_pVk, IC37x, IC37y, calldataload(add(pubSignals, 1152)))
                
                g1_mulAccC(_pVk, IC38x, IC38y, calldataload(add(pubSignals, 1184)))
                
                g1_mulAccC(_pVk, IC39x, IC39y, calldataload(add(pubSignals, 1216)))
                
                g1_mulAccC(_pVk, IC40x, IC40y, calldataload(add(pubSignals, 1248)))
                
                g1_mulAccC(_pVk, IC41x, IC41y, calldataload(add(pubSignals, 1280)))
                
                g1_mulAccC(_pVk, IC42x, IC42y, calldataload(add(pubSignals, 1312)))
                
                g1_mulAccC(_pVk, IC43x, IC43y, calldataload(add(pubSignals, 1344)))
                
                g1_mulAccC(_pVk, IC44x, IC44y, calldataload(add(pubSignals, 1376)))
                
                g1_mulAccC(_pVk, IC45x, IC45y, calldataload(add(pubSignals, 1408)))
                
                g1_mulAccC(_pVk, IC46x, IC46y, calldataload(add(pubSignals, 1440)))
                
                g1_mulAccC(_pVk, IC47x, IC47y, calldataload(add(pubSignals, 1472)))
                
                g1_mulAccC(_pVk, IC48x, IC48y, calldataload(add(pubSignals, 1504)))
                
                g1_mulAccC(_pVk, IC49x, IC49y, calldataload(add(pubSignals, 1536)))
                
                g1_mulAccC(_pVk, IC50x, IC50y, calldataload(add(pubSignals, 1568)))
                
                g1_mulAccC(_pVk, IC51x, IC51y, calldataload(add(pubSignals, 1600)))
                
                g1_mulAccC(_pVk, IC52x, IC52y, calldataload(add(pubSignals, 1632)))
                
                g1_mulAccC(_pVk, IC53x, IC53y, calldataload(add(pubSignals, 1664)))
                
                g1_mulAccC(_pVk, IC54x, IC54y, calldataload(add(pubSignals, 1696)))
                
                g1_mulAccC(_pVk, IC55x, IC55y, calldataload(add(pubSignals, 1728)))
                
                g1_mulAccC(_pVk, IC56x, IC56y, calldataload(add(pubSignals, 1760)))
                
                g1_mulAccC(_pVk, IC57x, IC57y, calldataload(add(pubSignals, 1792)))
                
                g1_mulAccC(_pVk, IC58x, IC58y, calldataload(add(pubSignals, 1824)))
                
                g1_mulAccC(_pVk, IC59x, IC59y, calldataload(add(pubSignals, 1856)))
                
                g1_mulAccC(_pVk, IC60x, IC60y, calldataload(add(pubSignals, 1888)))
                
                g1_mulAccC(_pVk, IC61x, IC61y, calldataload(add(pubSignals, 1920)))
                
                g1_mulAccC(_pVk, IC62x, IC62y, calldataload(add(pubSignals, 1952)))
                
                g1_mulAccC(_pVk, IC63x, IC63y, calldataload(add(pubSignals, 1984)))
                
                g1_mulAccC(_pVk, IC64x, IC64y, calldataload(add(pubSignals, 2016)))
                
                g1_mulAccC(_pVk, IC65x, IC65y, calldataload(add(pubSignals, 2048)))
                
                g1_mulAccC(_pVk, IC66x, IC66y, calldataload(add(pubSignals, 2080)))
                

                // -A
                mstore(_pPairing, calldataload(pA))
                mstore(add(_pPairing, 32), mod(sub(q, calldataload(add(pA, 32))), q))

                // B
                mstore(add(_pPairing, 64), calldataload(pB))
                mstore(add(_pPairing, 96), calldataload(add(pB, 32)))
                mstore(add(_pPairing, 128), calldataload(add(pB, 64)))
                mstore(add(_pPairing, 160), calldataload(add(pB, 96)))

                // alpha1
                mstore(add(_pPairing, 192), alphax)
                mstore(add(_pPairing, 224), alphay)

                // beta2
                mstore(add(_pPairing, 256), betax1)
                mstore(add(_pPairing, 288), betax2)
                mstore(add(_pPairing, 320), betay1)
                mstore(add(_pPairing, 352), betay2)

                // vk_x
                mstore(add(_pPairing, 384), mload(add(pMem, pVk)))
                mstore(add(_pPairing, 416), mload(add(pMem, add(pVk, 32))))


                // gamma2
                mstore(add(_pPairing, 448), gammax1)
                mstore(add(_pPairing, 480), gammax2)
                mstore(add(_pPairing, 512), gammay1)
                mstore(add(_pPairing, 544), gammay2)

                // C
                mstore(add(_pPairing, 576), calldataload(pC))
                mstore(add(_pPairing, 608), calldataload(add(pC, 32)))

                // delta2
                mstore(add(_pPairing, 640), deltax1)
                mstore(add(_pPairing, 672), deltax2)
                mstore(add(_pPairing, 704), deltay1)
                mstore(add(_pPairing, 736), deltay2)


                let success := staticcall(sub(gas(), 2000), 8, _pPairing, 768, _pPairing, 0x20)

                isOk := and(success, mload(_pPairing))
            }

            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))

            // Validate that all evaluations ∈ F
            
            checkField(calldataload(add(_pubSignals, 0)))
            
            checkField(calldataload(add(_pubSignals, 32)))
            
            checkField(calldataload(add(_pubSignals, 64)))
            
            checkField(calldataload(add(_pubSignals, 96)))
            
            checkField(calldataload(add(_pubSignals, 128)))
            
            checkField(calldataload(add(_pubSignals, 160)))
            
            checkField(calldataload(add(_pubSignals, 192)))
            
            checkField(calldataload(add(_pubSignals, 224)))
            
            checkField(calldataload(add(_pubSignals, 256)))
            
            checkField(calldataload(add(_pubSignals, 288)))
            
            checkField(calldataload(add(_pubSignals, 320)))
            
            checkField(calldataload(add(_pubSignals, 352)))
            
            checkField(calldataload(add(_pubSignals, 384)))
            
            checkField(calldataload(add(_pubSignals, 416)))
            
            checkField(calldataload(add(_pubSignals, 448)))
            
            checkField(calldataload(add(_pubSignals, 480)))
            
            checkField(calldataload(add(_pubSignals, 512)))
            
            checkField(calldataload(add(_pubSignals, 544)))
            
            checkField(calldataload(add(_pubSignals, 576)))
            
            checkField(calldataload(add(_pubSignals, 608)))
            
            checkField(calldataload(add(_pubSignals, 640)))
            
            checkField(calldataload(add(_pubSignals, 672)))
            
            checkField(calldataload(add(_pubSignals, 704)))
            
            checkField(calldataload(add(_pubSignals, 736)))
            
            checkField(calldataload(add(_pubSignals, 768)))
            
            checkField(calldataload(add(_pubSignals, 800)))
            
            checkField(calldataload(add(_pubSignals, 832)))
            
            checkField(calldataload(add(_pubSignals, 864)))
            
            checkField(calldataload(add(_pubSignals, 896)))
            
            checkField(calldataload(add(_pubSignals, 928)))
            
            checkField(calldataload(add(_pubSignals, 960)))
            
            checkField(calldataload(add(_pubSignals, 992)))
            
            checkField(calldataload(add(_pubSignals, 1024)))
            
            checkField(calldataload(add(_pubSignals, 1056)))
            
            checkField(calldataload(add(_pubSignals, 1088)))
            
            checkField(calldataload(add(_pubSignals, 1120)))
            
            checkField(calldataload(add(_pubSignals, 1152)))
            
            checkField(calldataload(add(_pubSignals, 1184)))
            
            checkField(calldataload(add(_pubSignals, 1216)))
            
            checkField(calldataload(add(_pubSignals, 1248)))
            
            checkField(calldataload(add(_pubSignals, 1280)))
            
            checkField(calldataload(add(_pubSignals, 1312)))
            
            checkField(calldataload(add(_pubSignals, 1344)))
            
            checkField(calldataload(add(_pubSignals, 1376)))
            
            checkField(calldataload(add(_pubSignals, 1408)))
            
            checkField(calldataload(add(_pubSignals, 1440)))
            
            checkField(calldataload(add(_pubSignals, 1472)))
            
            checkField(calldataload(add(_pubSignals, 1504)))
            
            checkField(calldataload(add(_pubSignals, 1536)))
            
            checkField(calldataload(add(_pubSignals, 1568)))
            
            checkField(calldataload(add(_pubSignals, 1600)))
            
            checkField(calldataload(add(_pubSignals, 1632)))
            
            checkField(calldataload(add(_pubSignals, 1664)))
            
            checkField(calldataload(add(_pubSignals, 1696)))
            
            checkField(calldataload(add(_pubSignals, 1728)))
            
            checkField(calldataload(add(_pubSignals, 1760)))
            
            checkField(calldataload(add(_pubSignals, 1792)))
            
            checkField(calldataload(add(_pubSignals, 1824)))
            
            checkField(calldataload(add(_pubSignals, 1856)))
            
            checkField(calldataload(add(_pubSignals, 1888)))
            
            checkField(calldataload(add(_pubSignals, 1920)))
            
            checkField(calldataload(add(_pubSignals, 1952)))
            
            checkField(calldataload(add(_pubSignals, 1984)))
            
            checkField(calldataload(add(_pubSignals, 2016)))
            
            checkField(calldataload(add(_pubSignals, 2048)))
            
            checkField(calldataload(add(_pubSignals, 2080)))
            

            // Validate all evaluations
            let isValid := checkPairing(_pA, _pB, _pC, _pubSignals, pMem)

            mstore(0, isValid)
             return(0, 0x20)
         }
     }
 }
