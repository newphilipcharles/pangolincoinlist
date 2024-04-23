// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;



// OpenZeppelin Contracts (last updated v4.9.0) (utils/math/Math.sol)
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                // Solidity will revert if denominator == 0, unlike the div opcode on its own.
                // The surrounding unchecked block does not change this fact.
                // See https://docs.soliditylang.org/en/latest/control-structures.html#checked-or-unchecked-arithmetic.
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1, "Math: mulDiv overflow");

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator, Rounding rounding) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10 ** result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 256, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result << 3) < value ? 1 : 0);
        }
    }
}
// OpenZeppelin Contracts (last updated v4.9.0) (utils/math/Math.sol)

// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}
// OpenZeppelin Contracts (last updated v4.9.4) (utils/Context.sol)


// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}
// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)


// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)
abstract contract Ownable is Context {
    address public _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// OpenZeppelin Contracts (last updated v4.9.0) (access/Ownable.sol)



interface IERC20 {
    function totalSupply() external view returns (uint);

    function balanceOf(address account) external view returns (uint);

    function transfer(address recipient, uint amount) external returns (bool);

    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint value);
    event Approval(address indexed owner, address indexed spender, uint value);
}


contract StakingContract is Ownable,Pausable {
    
    mapping(uint256 => string) public StakeKeys;
    uint256 private _rewardAmount;
    uint256 private immutable _packet50 = 50000000000000000000;         //MiningStake 50 Package
    uint256 private immutable _period1  = 7750000000000000;           //MiningStake 1.Period Reward for each 50 PRX
    uint256 private immutable _period2  = 6950000000000000;        //MiningStake 2.Period Reward
    uint256 private immutable _period3  = 6600000000000000;        //MiningStake 3.Period Reward


    mapping(address => StakeMapping) StakeMappings; //users can't take new loans before repaying

    struct StakeMapping {
        uint256 StakeAmount;
        uint256 period1;
        uint256 period2;
        uint256 period3;
        uint256 package50cnt;
    }
    
    // OpenZeppelin Contracts (last updated v4.9.0) (security/ReentrancyGuard.sol)
    modifier nonReentrant {
        require(!_entered, "re-entrant call");
        _entered = true;
        _;
        _entered = false;
    }
    // OpenZeppelin Contracts (last updated v4.9.0) (security/ReentrancyGuard.sol)


    address[] public StakeKeysList;

    address[] public Validators;
    
    uint256 public validatorFee = 14;
    function validatorAdd(address _validatorAddress) public onlyOwner () {
        Validators.push(_validatorAddress);
    }
    function removeValidator(address _validatorAddress) public onlyOwner {
        for (uint i = 0; i < Validators.length; i++) {
            if (Validators[i] == _validatorAddress) {
                Validators[i] = Validators[Validators.length - 1];
                Validators.pop();
                break;
            }
        }
    }



    function ValidatorCount() public view returns (uint256) {
        return Validators.length;
    }
    function ValidatorsetFee(uint256 _fee) public onlyOwner {
        require(_fee <= 14,"validator Fee Max %14");
        require(_fee > 0,"validator Fee Min %1");
        validatorFee = _fee;
    }

    bool private _entered;
    IERC20 public immutable stakingToken;

    constructor(address _stakingToken) {
        Ownable(msg.sender);
        stakingToken = IERC20(_stakingToken);
        _owner = msg.sender;
    }

    function pause() public onlyOwner {
        _pause();
    }

    function unpause() public onlyOwner {
        _unpause();
    }

    event Stake(address indexed _StakeOwner, uint256 _rewardAmount, uint256 _startTime, uint256 _endTime);
    
    function packageType(uint256 _StakeAmount) internal pure returns (uint256) {
        return _StakeAmount /  _packet50;
    }

    function stakeIT(address _StakeOwner,uint256 _StakeAmount ,uint256 _dayfinish)  internal nonReentrant  { 
       require(packageType(_StakeAmount) > 0 ,"value must be > 0 ");
        require(stakingToken.approve(msg.sender, _rewardAmount));
        require(stakingToken.transferFrom(msg.sender, address(this), _StakeAmount));

        
        uint256  _startTime = block.timestamp;
        uint256  _endTime;
        if (_startTime < 1713128400 ) {
            _endTime = _startTime + (_dayfinish * 1 days);
        } else {
            _endTime = _startTime + 365 days;    
        }
        uint256 _p50_cnt = 0;

      
     
        uint256 _p1;
        uint256 _p2;
        uint256 _p3;
        uint256 _px;

        _p50_cnt = packageType(_StakeAmount); 
        (_p1,_p2,_p3,_px) = AddAmount(_startTime,_endTime);
        uint256 _totalAmount = (_p1  * (_period1 * _p50_cnt)) + (_p2 * (_period2 * _p50_cnt)) + (_p3 * (_period3 * _p50_cnt));
        StakeMapping storage stakemapping = StakeMappings[_StakeOwner] ;

        stakemapping.StakeAmount += _totalAmount;
        stakemapping.period1 += _p1 * _p50_cnt;
        stakemapping.period2 += _p2 * _p50_cnt;
        stakemapping.period3 += _p3 * _p50_cnt;
        stakemapping.package50cnt += _p50_cnt;
        
        if (stakeIfexist(_StakeOwner) == false) {
          StakeKeysList.push(_StakeOwner);
        }
        emit Stake(_StakeOwner, _rewardAmount, _startTime,_endTime);
        
    }

    function stakeIfexist(address _stakeOwner) public view returns (bool) {
        for (uint i = 0; i < StakeKeysList.length; i++) {
            address listStakeKey = StakeKeysList[i];
            if (listStakeKey == _stakeOwner) {
                return true;
            }
        }
        return false;
    }



    function AddAmount(uint256 _startDate, uint256 _endDate) internal pure  returns(uint256,uint256,uint256,uint256) {
        uint256 xa1 = 0;
        uint256 xa2 = 0;
        uint256 xa3 = 0;
        uint256 xb1 = 0;
        uint256 xb2 = 0;
        uint256 xb3 = 0;
        
        uint256 Halving1 = 1728939600;
        uint256 Halving2 = 1760475600;
        uint256 Halving3 = 1792011600;

        if(_endDate < Halving1) {
            xa1 = _endDate - _startDate ;
            xb1 = xa1 / 3600;

            return (xb1 , xb2, xb3,1);
            //155
        } else if(_endDate < Halving2) {
            xa1 = Halving1 - _startDate;
            xb1 = xa1 / 3600;
        

            xa2 = _endDate - Halving1;

            xb2 = xa2 / 3600;

            return (xb1,xb2,xb3,2);
            //return 139;
        } else if(_endDate < Halving3) {
            xa2 =  Halving2 - _startDate ;
            xb2 = xa2 / 3600;

            xa3 = _endDate - Halving2;
            xb3 = xa3 / 3600;

            return (xb1,xb2,xb3,3);

        } else {
            xb3 = 8766;



            return (xb1,xb2,xb3,4);
    
            //return 132;
        }         
    }
    function removeStakeKeysList(address _stakeOwner) public onlyOwner {
        address myStakeKey = _stakeOwner;
        for (uint i = 0; i < StakeKeysList.length; i++) {
            address listStakeKey = StakeKeysList[i];
            if (myStakeKey == listStakeKey) {
                StakeKeysList[i] = StakeKeysList[StakeKeysList.length - 1];
                StakeKeysList.pop();
                break;
            }
        }
    }

    function getReward(uint256 _start,uint256 _finish) external whenNotPaused onlyOwner {
            
            uint256 validatorTotalFee = 0;
            uint256 tempValidatorFee = 0;
            if (StakeKeysList.length < _start) {

            } else {

                if(_finish > StakeKeysList.length ) {
                    _finish = StakeKeysList.length;
                }
                for (uint i = _start; i < _finish; i++) {
                    address _stakeOwner= StakeKeysList[i];
                    StakeMapping storage stakemapping = StakeMappings[_stakeOwner];
                    
                    uint256 _ptype = stakemapping.package50cnt;

                    address payable _StakeOwner = payable(_stakeOwner);
                    if (stakemapping.StakeAmount >= 0) {
                    if (stakemapping.period1 > 0) {
                        _rewardAmount= (_period1 * _ptype);
                        stakemapping.period1 -= _ptype;
                    } else if (stakemapping.period2 > 0) {
                        _rewardAmount= (_period2 * _ptype);
                        stakemapping.period2 -= _ptype;
                    } else if (stakemapping.period3 > 0) {
                        _rewardAmount= (_period3 * _ptype);
                        stakemapping.period3 -= _ptype;
                    } else {
                        _rewardAmount = 0;
                    }
                    if (_rewardAmount > 0) {

                        tempValidatorFee = (_rewardAmount / 100) * validatorFee;

                        _rewardAmount = _rewardAmount - tempValidatorFee;

                        validatorTotalFee += tempValidatorFee;


                        require(stakingToken.approve(address(this), _rewardAmount));
                        require(stakingToken.transferFrom(address(this),_StakeOwner, _rewardAmount));
                            
                        stakemapping.StakeAmount -=  _rewardAmount;
                    }
                    }
                }
                if (validatorTotalFee > 0 && Validators.length > 0) {
                    tempValidatorFee = validatorTotalFee / Validators.length;
                    for (uint i = 0; i < Validators.length; i++) {
                        address payable  validatorAddress= payable(Validators[i]);

                        require(stakingToken.approve(address(this), tempValidatorFee));
                        require(stakingToken.transferFrom(address(this),validatorAddress, tempValidatorFee));
                    }
                }
            }          
            
       
    }
    

    function stakeListgetLength() public view  returns (uint256) {
        return StakeKeysList.length;
    }

    
    
    function stakeITBalance(address _StakeOwner) public view  returns( StakeMapping memory) {
        StakeMapping memory stakemaping = StakeMappings[_StakeOwner];        
        return  stakemaping ;        
    }
    
    
    function stakePRXToContract(address _StakeOwner ,uint256 _value,uint256 _dayfinish  )  payable external {
        require(_value > 0,"value must be > 0 ");        
        stakeIT(_StakeOwner,_value,_dayfinish);
    }


    uint public receiveCount = 0;
    uint public fallbackCount = 0;
    
    
    receive()  external payable onlyOwner
    {
        require(msg.value > 0,"value must be > 0 ");

        receiveCount += 1;
    }
    
    
    fallback() external payable onlyOwner {
   
        require(msg.value > 0,"value must be > 0 ");

        fallbackCount += 1;

        
    }
     


}
