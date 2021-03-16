// SPDX-License-Identifier: GPL-3.0
pragma solidity ^0.8.0;

//  _    _           _      _____      _   
// | |  | |         | |    / ____|    | |      This is the Main Contract of HashCat.farm which
// | |__| | __ _ ___| |__ | |     __ _| |_     outputs a total amount of 17500 Tokens.   
// |  __  |/ _` / __| '_ \| |    / _` | __|    
// | |  | | (_| \__ \ | | | |___| (_| | |_     
// |_|  |_|\__,_|___/_| |_|\_____\__,_|\__| 
//                                         
                                         
import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";
import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/token/ERC20/SafeERC20.sol";
import "https://github.com/OpenZeppelin/openzeppelin-contracts/contracts/math/SafeMath.sol";

contract HashCat is ERC20 {
    
    using SafeERC20 for IERC20;
    using SafeMath for uint256;
    
    uint256 TotalSupply = 17500*(10**18);
    
    IERC20 private HashCatFees;
    
    address private farmManager;
    address private farmManagerAddress;
    
    //This constructor is only called once - when contract is deployed.
    constructor() payable ERC20("HashCat.farm", "HASH") {
        farmManager = msg.sender;
        _mint(msg.sender, TotalSupply);
    }
    
    modifier _isFarmManager() {
        require(msg.sender == farmManager, "Only the Farm Manager can interact with this function.");_;
    }
    
    function transferFees(uint256 amount) public _isFarmManager {
        HashCatFees.safeTransfer(farmManagerAddress, amount);
    }
    
    function getFarmManager() public view returns(address){
        return farmManager;
    }
    
    function getFarmManagerAddress() public view returns(address){
        return farmManagerAddress;
    }
    
    function setHashingContract(address hashingContract) public _isFarmManager {
        HashCatFees = IERC20(hashingContract);
    }
    
    function setFarmManagerAddress(address farmaddress) public _isFarmManager {
        farmManagerAddress = farmaddress;
    }
}
