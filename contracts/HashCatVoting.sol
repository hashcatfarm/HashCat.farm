// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

//  _    _           _      _____      _   
// | |  | |         | |    / ____|    | |      This contract is the voting contract of
// | |__| | __ _ ___| |__ | |     __ _| |_     Hashcat.farm
// |  __  |/ _` / __| '_ \| |    / _` | __|    
// | |  | | (_| \__ \ | | | |___| (_| | |_     
// |_|  |_|\__,_|___/_| |_|\_____\__,_|\__| 
//                        

import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";
import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";
import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/math/SafeMath.sol";

contract HashCatVoting is ERC20 {
    
    struct Voter{
        uint256 tokenQuantity;
    }
    
    using SafeERC20 for IERC20;
    using SafeMath for uint256;
    
    address private farmManager;
    address private HashCatToken = 0xca1AA93724be5F7459D76c6DE984D22C9fBcB7Aa;
    IERC20 private HASH = IERC20(0xca1AA93724be5F7459D76c6DE984D22C9fBcB7Aa);
        
    mapping(address => Voter) private _user;
    
    bool votingStarted;
    
    uint256 _voteYes;
    uint256 _voteNo;
    uint256 _startingBlock;
    uint256 _futureSafetyBlock;
    uint256 _safetyBlock = 84000; //3 Days based on BSC Block Time
    // The safety block is used in case FarmManager doesn't unlock Tokens himself, forgets to or dies.
 
    constructor() payable ERC20("HashCat.farm Voting", "HASH") {
        farmManager = msg.sender;
        votingStarted = false;
        _voteYes = 0;
        _voteNo = 0;
    }
    
    event voteYesEvent(address indexed user, uint256 amount, uint256 voteYes);
    event voteNoEvent(address indexed user, uint256 amount, uint256 voteNo);
    event WithdrawTokens(address indexed user, uint256 amount);

    modifier _isFarmManager() {
        require(msg.sender == farmManager, "Only the Farm Manager can interact with this function.");_;
    }
    
    function getHashCatTokenAddress() public view returns(address){
        return HashCatToken;
    }
    
    function getHashCatIERC20TokenAddress() public view returns(IERC20){
        return HASH;
    }
    
    function resetVoting() public _isFarmManager{
        _voteYes = 0;
        _voteNo = 0;
        votingStarted = false;
    }
    
    function startVoting() public _isFarmManager{
        votingStarted = true;
        _startingBlock = block.number;
        _futureSafetyBlock = _startingBlock + _safetyBlock;
    }
    
    function getVotingState() public view returns(bool){
        return votingStarted;
    }
    
    function getCurrentBlock() public view returns(uint256){
        return block.number;
    }

    function getStartingBlock() public view returns(uint256){
        require(votingStarted == true, "You can get starting block only when vote is on-going.");
        return _startingBlock;
    }
    
    function getFutureSafetyBlock() public view returns(uint256){
        require(votingStarted == true, "You can get future block only when vote is on-going.");
        return _futureSafetyBlock;
    }
    
    function getYesVotes() public view returns(uint256){
        return _voteYes;
    }
    
    function getNoVotes() public view returns(uint256){
        return _voteNo;
    }
    
    function getTokensToWithdraw() public view returns(uint256){
        return _user[msg.sender].tokenQuantity;
    }
    
    function voteYes(uint256 amount) public{
        require(votingStarted == true, "You can vote only when the vote is on-going.");
        require(block.number < _futureSafetyBlock, "You cannot vote right now");
        _voteYes = _voteYes.add(amount);
        _user[msg.sender].tokenQuantity = _user[msg.sender].tokenQuantity.add(amount);
        HASH.safeTransferFrom(msg.sender, address(this), amount);
        emit voteYesEvent(msg.sender, amount, _voteYes);
    }
    
    function voteNo(uint256 amount) public{
        require(votingStarted == true, "You can vote only when the vote is on-going.");
        require(block.number < _futureSafetyBlock, "You cannot vote right now");
        _voteNo = _voteNo.add(amount);
        _user[msg.sender].tokenQuantity = _user[msg.sender].tokenQuantity.add(amount);
        HASH.safeTransferFrom(msg.sender, address(this), amount);
        emit voteNoEvent(msg.sender, amount, _voteNo);
    }
    
    function withdrawTokens() public{
        require(votingStarted == false || block.number > _futureSafetyBlock, "You can withdraw only once the vote is finished.");
        require(_user[msg.sender].tokenQuantity > 0, "You dont have tokens to withdraw.");
        HASH.safeTransfer(msg.sender, _user[msg.sender].tokenQuantity);
        _user[msg.sender].tokenQuantity = _user[msg.sender].tokenQuantity.sub(_user[msg.sender].tokenQuantity);
        emit WithdrawTokens(msg.sender, _user[msg.sender].tokenQuantity);
    }
}
